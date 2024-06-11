# coding: tilde

from pano.prettify import pprint_trace, pretty_stor
from pano.matcher import match, Any

from utils.helpers import opcode, find_f, replace, replace_f, tuplify, replace_lines, get_op, hashable,  to_exp2

from core.algebra import minus_op, safe_le_op, divisible_bytes, to_bytes

from core.masks import mask_to_type

from utils.helpers import COLOR_GREEN, COLOR_GRAY, ENDC

import logging

logger = logging.getLogger(__name__)


'''
    helpers

'''

def get_loc(exp):
    def f(exp):
        if type(exp) != tuple:
            return None

        elif opcode(exp) in ('storage', 'stor'):
#        elif exp ~ ('storage', ...): # if we have a storage reference within the storage
                                     # don't follow this one when looking for loc
            return None

        elif m := match(exp, ('loc', ':num')):
            return m.num

        elif m := match(exp, ('name', Any, ':num')):
            return m.num

        else:
            for e in exp:
                if (loc:=f(e)) is not None:
                    return loc

            return None

    if m := match(exp, ('type', Any, ('field', Any, ':m_idx'))):
        exp = m.m_idx

    if m := match(exp, ('storage', Any, Any, ':e')):
        exp = m.e

    if m := match(exp, ('stor', Any, Any, ':e')):
        exp = m.e

    if m := match(exp, ('stor', ':e')):
        exp = m.e

    return f(exp)


def get_name_full(exp):
    def f(exp):
        if type(exp) != tuple:
            return None

        elif opcode(exp) in ('stor', 'storage'):#exp ~ ('storage', ...): # if we have a storage reference within the storage
                                     # don't follow this one when looking for loc
            return None

        elif exp ~ ('name', :name, _):
            return exp

        else:
            for e in exp:
                if (loc:=f(e)) is not None:
                    return loc

            return None

    if exp ~ ('type', _, ('field', _, :m_idx)):
        exp = m_idx

    if exp ~ ('storage', _, _, :e):
        exp = e

    if exp ~ ('stor', _, _, :e):
        exp = e

    if exp ~ ('stor', :e):
        exp = e

    return f(exp)

def get_name(exp):
    r = get_name_full(exp)
    if r is None:
        return None
    else:
        return match(r, ('name', ':name', Any)).name


def find_stores(exp):

    if exp ~ ('store', :size, :off, :idx, :val):
        res = {('storage', size, off, idx)}

    elif exp ~ ('storage', _, _, _):
        res = {exp}

    else:
        res = set()

    if type(exp) == tuple or type(exp) == list:
        for e in exp:
            res = res.union(find_stores(e))

    return res


'''
    proper

'''

def rewrite_functions(functions):
    '''
        rewrites functions, putting storage names there,
        then detects storage types and returns a list of those in a form of
        ('def', name, loc, type)
        that can be displayed by pretty_type from prettify

    '''

    storages = list(find_stores([f.trace for f in functions]))

    # (storage 256 0 (sha3 (cd 4) 7)
    # -> (storage 256 0 (array (cd 4) (loc 7)))

    # (storage 256 0 6)
    # (storage 256 0 (loc 6))
    # (storage 256 0 (length (loc 6))
    # (storage 256 0 (array idx (loc 6))
    # (storage 256 0 (map idx (loc 6))


    storages_assoc = _sparser(storages)

    names = find_storage_names(functions)
    replace_names_in_assoc(names, storages_assoc)
    replace_names_in_assoc_bool(names, storages_assoc)


    for func in functions:
        func.trace = repl_stor(func.trace, storages_assoc)

    stordefs = {}

    for src, dest in storages_assoc.items():
        d = dest
        loc = get_loc(d)
        if loc is None: loc = 99

        assert loc is not None, d
        if loc not in stordefs:
            stordefs[loc] = set()

        if type(loc) != int:
            continue

        stordefs[loc].add(d)

    def get_type(stordefs):
        sizes = set()
        offsets = set()
        for s in stordefs:
            if s ~ ('stor', :size, :off, (:op, :idx, ...)) and op in ('map', 'array'):
                sizes.add(size)
                if safe_le_op(0, off) is True:
                    offsets.add(off)

        if 256 in sizes:
            sizes.remove(256)

        if 0 in offsets:
            offsets.remove(0)

        if len(offsets) > 0:
            # for structs, find their size by looking at how the index is multiplied

            for s in stordefs:
                if s ~ ('stor', _, _, (:op, :idx, ...)) and op in ('map', 'array'):
                    if idx ~ ('stor', _, int:siz, ('length', ...)) and siz < 0:
                        return ('struct', -siz + 1)

            return 'struct'

        if len(sizes) == 0:
            return 256
        else:
            return min(sizes)

    defs = []

    def sort(it):
        try:
            return sorted(it)
        except Exception:
            return sorted(it, key=str)

    for loc in sort(stordefs.keys()):
            for l in sort(stordefs[loc]):
                if match(l, ('stor', int, int, ('loc', Any))) or match(l, ('stor', int, int, ('name', ...))):
                    continue

                name = get_name(l)
                if name is None:
                    name = 'stor' + str(loc)

                if m := match(l, ('stor', int, int, ':idx')):
                    idx = m.idx
                    if opcode(idx) == 'map':
                        defs.append(('def', name, loc, ('mapping', get_type(stordefs[loc]))))
                    elif opcode(idx) in ('array', 'length'):
                        defs.append(('def', name, loc, ('array', get_type(stordefs[loc]))))

                break

            # This is executed if we didn't add any defs in the loop above.
            else:
                # all stor references are not arrays/maps, let's just print them out
                for l in sort(stordefs[loc]):
                    name = get_name(l)

                    if name is None:
                        if type(loc) == int and loc >= 1000:
                            name = 'stor' + hex(loc)[2:6].upper()
                        else:
                            name = 'stor' + str(loc)

                    defs.append(('def', name, loc, ('mask', l[1], l[2])))


    return defs


def to_stordef(exp):
    return exp
    if opcode(exp) in ('mask_shl', 'cd', 'storage', 'var'):
        return 'idx'

    if type(exp) == tuple:
        return tuple(to_stordef(e) for e in exp)
    else:
        return exp


'''

'''

def repl_stor(exp, assoc):
    if type(exp) == list:
        return [repl_stor(e, assoc) for e in exp]

    if opcode(exp) == "store":
        _, size, off, idx, val = exp
        dest = assoc[('storage', size, off, idx)]
        return ('store', ) + dest[1:] + (repl_stor(val, assoc), )

    elif hashable(exp) and exp in assoc:
        return assoc[exp]

    elif type(exp) == tuple:
        return tuple([repl_stor(e, assoc) for e in exp])

    else:
        return exp


used_locs = set()

def replace_names_in_assoc_bool(names, storages_assoc):
    # we are replacing bools only after the other storage
    # because in some situations there are functions like
    # areTokensAvailable == bool(tokens.length)
    # and, if possible we don't want to use this getter's name for such purpose
    #
    # there are better/more precise ways to handle this though
    for getter, name in names.items():
        if not (getter ~ ('bool', ('storage', :size, :off, int:loc))):
            continue

        if ('array', loc) in used_locs:
            pass
        elif ('stor', size, off, loc) in used_locs:
            pass
        else:
            for src, pattern in storages_assoc.items():
#                print(pattern)
                if pattern == ('stor', size, off, ('loc', loc)):
                    storages_assoc[src] = ('stor', size, off, ('name', name, loc))


def replace_names_in_assoc(names, storages_assoc):
    for pattern, name in names.items():

        if opcode(pattern) == 'bool':
            continue

        if opcode(pattern) == 'struct':
            stor_id = pattern
        else:
            stor_id = storages_assoc[pattern]

        if stor_id ~ ('stor', :size, :off, ('loc', :num)):
            # if we found a simple getter for a storage number,
            # we need to check first if a given location is only accessed
            # this way. otherwise it may be a function like getLength, that
            # returns the array length, and we don't want to use it as a storage name
            if all(match(pattern, ('stor', Any, Any, ('loc', Any))) \
                   for pattern in storages_assoc if get_loc(pattern) == num):

                used_locs.add(stor_id)

                for src, pattern in storages_assoc.items():
                    if pattern == stor_id:
                        storages_assoc[src] = ('stor', size, off, ('name', name, num))

        elif stor_id ~ ('stor', _, _, ('map', _, :loc)) or \
             stor_id ~ ('stor', _, _, ('array', _, :loc)) or \
             stor_id ~ ('struct', :loc):

            # for arrays, we don't want 'address' at the end of the name. looks better
            new_name = name.split('Address')[0]
            if len(new_name) > 0:
                name = new_name

            loc_id = get_loc(loc)
            used_locs.add(('array', loc_id))

            for src, pattern in storages_assoc.items():
                if get_loc(pattern) == loc_id:
                    pattern = replace(pattern, ('loc', loc_id), ('name', name, loc_id))
                    storages_assoc[src] = pattern

        else:
            logger.warning('storage pattern not found')


'''
    find storage names based on function name
'''

def find_storage_names(functions):

    res = {}

    for func in functions:
        trace = func.trace

        if func.getter:
            getter = func.getter

            assert opcode(getter) in ('storage', 'struct', 'bool')

            # func name into potential storage name

            new_name = func.name

            if new_name[:3] == 'get' and len(new_name.split('(')[0])>3:
                new_name = new_name[3:]

            if new_name != new_name.upper():
                # otherwise we get stuff like bILLIONS in 0x48fa97aDb417367a480D6b93FBC26CB0B8E93F5a
                new_name = new_name[0].lower() + new_name[1:]

            new_name = new_name.split('(')[0]

            if match(getter, ('storage', 160, ...)):
                if ('address' not in new_name.lower()) and \
                   ('addr' not in new_name.lower()) and \
                   ('account' not in new_name.lower()) and \
                   ('owner' not in new_name.lower()):
                        new_name += 'Address'

            res[getter] = new_name

    return res

'''
    sparser proper
'''



def mask_to_mul(exp):
    if exp ~ ('mask_shl', int:size, int:offset, int:shl, :val):
        if shl > 0 and offset == 0 and size == 256 - shl:
            if shl <= 8:
                return ('mul', 2**shl, val)

        if shl < 0 and offset == -shl and size == 256 - offset:
            if shl >= -8:
                return ('div', 2**shl, val)

    return exp

def stor_replace_f(storages, f):
    def internal_f(exp, f):
        if exp ~ ('storage', ...):
            return exp

        if type(exp) == tuple:
            exp = tuple(internal_f(e, f) for e in exp)

        return f(exp)


    res = []
    for stor in storages:
        assert stor ~ ('stor', :size, :off, :idx)

        res.append(('stor', size, off, internal_f(idx, f)))

    return res

def _sparser(orig_storages):

    storages = []
    for idx, s in enumerate(orig_storages):
        storages.append(('stor', )+s[1:])

    def simplify_sha3(e):
        e = rainbow_sha3(e)

        if e ~ ('sha3', ('data', *terms)):
            e = ('sha3', ) + terms
        if e ~ ('sha3', int:loc):
            return ('loc', e[1])
        elif e ~ ('sha3', ('sha3', *terms), int:loc):
            return ('map', ('data', *terms), ('loc', loc))
        elif e ~ ('sha3', :idx, int:loc):
            return ('map', idx, ('loc', loc))
        else:
            return e

    storages = stor_replace_f(storages, simplify_sha3)

    '''
        is add a struct or a loc?
    '''

    res = []
    for s in storages:
        if s ~ ('stor', :size, ('mask_shl', :o_size, :o_off, :o_shl, :arr_idx), :idx) and size == 2**o_shl:
            new_osize = minus_op(o_size)
            if idx ~ ('add', int:num, _):
                idx = num
            s = ('stor', size, 0, ('array', ('mask_shl', o_size+o_shl, o_off, 0, arr_idx), ('loc', idx)))

        res.append(s)

    storages = res

    storages = stor_replace_f(storages, mask_to_mul)

    res = []
    for s in storages:
        assert s ~ ('stor', :size, :offset, :idx)

        if idx ~ ('add', int:num, *terms) and get_loc(terms) is not None:
            offset += 256 * num
            idx = ('add', ) + terms

        res.append(('stor', size, offset, idx))

    storages = res

    '''

        array is when you add to a loc

    '''

    def add_to_arr(exp):
        if exp ~ ('add', :left, :right):
            if opcode(left) == 'loc':
                right, left = left, right

            if opcode(right) == 'loc':
                return ('array', left, right)

        return exp

    storages = replace_f(storages, add_to_arr)

    '''

        (s 256 0 (add 3 (mul 0.125 idx)))

    '''

    res = []
    for s in storages:
        assert s ~ ('stor', :size, :offset, :idx)

        idx ~ ('add', :idx)

        if idx ~ ('add', ...) and get_loc(idx) is None:
            if idx ~ ('add', int:loc, :pos):
                s = ('stor', size, offset, ('array', pos, ('loc', loc)))
            else:
                logger.warning(f'Weird storage index, {idx}')

        res.append(s)

    storages = res

    '''

        convert regular storages into lengths or locs

        that is - find all the idxs that (stor _ _ idx) exists
                  but are also referenced through (stor _ _ (sth... (loc idx)))

    '''

    assert len(storages) == len(orig_storages)


    res = []
    for s in storages:
        assert s ~ ('stor', :size, :offset, :idx)

        if type(idx) == int:

            if str(('loc', idx)) in str(storages):
                assert type(idx) == int, idx
                idx = ('length', ('loc', idx))

            else:
                idx = ('loc', idx)

        res.append(('stor', size, offset, idx))
    storages = res

    '''
        cleanup of nested maps

    '''
    res = []
    for s in storages:

        if s ~ ('stor', :size, :off, ('range', ('array', :beg, :loc), :end)):
            s = ('stor', size, off, ('array', ('range', beg, end), loc))

        res.append(s)

    storages = res


    def double_map(exp):
        exp ~ ('add', :exp) # remove 'add' with just one term. should be somewhere else
        if exp ~ ('sha3', ('map', *terms)):
            return ('map', *terms) # this is sth weird, see 0x48fa97aDb417367a480D6b93FBC26CB0B8E93F5a, transferFrom
        if exp ~ ('sha3', :idx, ('map', *terms)):
            return ('map', idx, ('map', *terms))

        if exp ~ ('add', :idx, ('map', *terms)):
            return ('array', idx, ('map', *terms))
        if exp ~ ('sha3', :idx, :loc):
            return ('map', idx, loc)


        # this all should be recursive
        if exp ~ ('add', ('sha3', ('array', *terms)), :num):
            return ('array', num, ('array', )+terms)
        if exp ~ ('add', :num, ('sha3', ('array', *terms))):
            return ('array', num, ('array', )+terms)

        if exp ~ ('sha3', ('array', :idx, :loc)):
            return ('array', idx, loc)


        if exp ~ ('add', ('map', *terms), :num):
            return ('array', num, ('map', )+terms)
        if exp ~ ('add', :num, ('map', *terms)):
            return ('array', num, ('map', )+terms)

        if exp ~ ('add', ('var', :x), ('array', :idx, :loc)):
            return ('array', ('add', idx, ('var', x)), loc)

        if exp ~ ('add', ('array', :idx, :loc), ('var', :x)):
            return ('array', ('add', idx, ('var', x)), loc)


        return exp

    storages = replace_f(storages, double_map)

    assert len(storages) == len(orig_storages)

    '''

        let's make a dict with output...

    '''

    res = {}
    for idx, s in enumerate(orig_storages):
        dst = storages[idx]
        res[s] = dst

    '''

        and replace storage definitions in it recursively

    '''

    def repl_res(exp):
        if type(exp) != tuple:
            return exp

        if exp in res:
            exp = res[exp]

        return tuple([repl_res(e) for e in exp])

    new_res = {}
    for src, dest in res.items():
        new_res[src] = repl_res(dest)
        assert 'storage' not in str(new_res[src])

    res = new_res

    return res


'''
    data
'''

# to generate additional
# Web3.sha3(b'\x00'*31+b'\x01') == ('loc', 1)
'''
>>> for i in range(20):
...     h = Web3.sha3(b'\x00'*31 + bytes([i])).hex()
...     print(f"'{h}': ('loc':{i}),")
... '''


def rainbow_sha3(exp):
    if type(exp) == int and len(hex(exp)) > 40:
        for src, dest in sha3_loc_table.items():
            if hex(exp) in src:
                # sometimes the last bytes of exp are cut off (e.g. in ED), that's why
                # we're not doing exact matches. should check why they are cut off though
                # perhaps there's some problem with mask processing in whiles
                return dest

    return exp

sha3_loc_table = {
#0x7050c9e0f4ca769c69bd3a8ef740bc37934f8e2c036e5a723fd8ee048ed3f8c3 == ('sha3', 'org.zeppelinos.proxy.implementation')
    # source: https://github.com/zeppelinos/labs/blob/master/initializer_with_sol_editing/contracts/UpgradeabilityProxy.sol
    # ^ not replacing, because rest of the system doesn't handle arbitrary string locations
    '0x48fa97aDb417367a480D6b93FBC26CB0B8E93F5a': ('loc', 0),
    '0x48fa97aDb417367a480D6b93FBC26CB0B8E93F5a': ('loc', 1),
    '0x48fa97aDb417367a480D6b93FBC26CB0B8E93F5a': ('loc', 2),
    '0x48fa97aDb417367a480D6b93FBC26CB0B8E93F5a': ('loc', 3),
    '0x48fa97aDb417367a480D6b93FBC26CB0B8E93F5a': ('loc', 4),
    '0x48fa97aDb417367a480D6b93FBC26CB0B8E93F5a': ('loc', 5),
    '0x48fa97aDb417367a480D6b93FBC26CB0B8E93F5a': ('loc', 6),
    '0x48fa97aDb417367a480D6b93FBC26CB0B8E93F5a': ('loc', 7),
    '0x48fa97aDb417367a480D6b93FBC26CB0B8E93F5a': ('loc', 8),
    '0x48fa97aDb417367a480D6b93FBC26CB0B8E93F5a': ('loc', 9),
    '0x48fa97aDb417367a480D6b93FBC26CB0B8E93F5a': ('loc', 10),
    '0x48fa97aDb417367a480D6b93FBC26CB0B8E93F5a': ('loc', 11),
    '0x48fa97aDb417367a480D6b93FBC26CB0B8E93F5a': ('loc', 12),
    '0x48fa97aDb417367a480D6b93FBC26CB0B8E93F5a': ('loc', 13),
    '0x48fa97aDb417367a480D6b93FBC26CB0B8E93F5a': ('loc', 14),
    '0x48fa97aDb417367a480D6b93FBC26CB0B8E93F5a': ('loc', 15),
    '0x48fa97aDb417367a480D6b93FBC26CB0B8E93F5a': ('loc', 16),
    '0x48fa97aDb417367a480D6b93FBC26CB0B8E93F5a': ('loc', 17),
    '0x48fa97aDb417367a480D6b93FBC26CB0B8E93F5a': ('loc', 18),
    '0x48fa97aDb417367a480D6b93FBC26CB0B8E93F5a': ('loc', 19),
    '0x48fa97aDb417367a480D6b93FBC26CB0B8E93F5a' : ('map', 0, ('loc', 0)),
    '0x48fa97aDb417367a480D6b93FBC26CB0B8E93F5a' : ('map', 0, ('loc', 1)),
    '0x48fa97aDb417367a480D6b93FBC26CB0B8E93F5a' : ('map', 0, ('loc', 2)),
    '0x48fa97aDb417367a480D6b93FBC26CB0B8E93F5a' : ('map', 0, ('loc', 3)),
    '0x48fa97aDb417367a480D6b93FBC26CB0B8E93F5a' : ('map', 0, ('loc', 4)),
    '0x48fa97aDb417367a480D6b93FBC26CB0B8E93F5a' : ('map', 0, ('loc', 5)),
    '0x48fa97aDb417367a480D6b93FBC26CB0B8E93F5a' : ('map', 0, ('loc', 6)),
    '0x48fa97aDb417367a480D6b93FBC26CB0B8E93F5a' : ('map', 0, ('loc', 7)),
    '0x48fa97aDb417367a480D6b93FBC26CB0B8E93F5a' : ('map', 0, ('loc', 8)),
    '0x48fa97aDb417367a480D6b93FBC26CB0B8E93F5a' : ('map', 0, ('loc', 9)),
    '0x48fa97aDb417367a480D6b93FBC26CB0B8E93F5a' : ('map', 0, ('loc', 10)),
    '0x48fa97aDb417367a480D6b93FBC26CB0B8E93F5a' : ('map', 0, ('loc', 11)),
    '0x48fa97aDb417367a480D6b93FBC26CB0B8E93F5a' : ('map', 0, ('loc', 12)),
    '0x48fa97aDb417367a480D6b93FBC26CB0B8E93F5a' : ('map', 0, ('loc', 13)),
    '0x48fa97aDb417367a480D6b93FBC26CB0B8E93F5a' : ('map', 0, ('loc', 14)),
    '0x48fa97aDb417367a480D6b93FBC26CB0B8E93F5a' : ('map', 0, ('loc', 15)),
    '0x48fa97aDb417367a480D6b93FBC26CB0B8E93F5a' : ('map', 0, ('loc', 16)),
    '0x48fa97aDb417367a480D6b93FBC26CB0B8E93F5a' : ('map', 0, ('loc', 17)),
    '0x48fa97aDb417367a480D6b93FBC26CB0B8E93F5a' : ('map', 0, ('loc', 18)),
    '0x48fa97aDb417367a480D6b93FBC26CB0B8E93F5a' : ('map', 0, ('loc', 19)),
    '0x48fa97aDb417367a480D6b93FBC26CB0B8E93F5a' : ('map', 1, ('loc', 0)),
    '0x48fa97aDb417367a480D6b93FBC26CB0B8E93F5a' : ('map', 1, ('loc', 1)),
    '0x48fa97aDb417367a480D6b93FBC26CB0B8E93F5a' : ('map', 1, ('loc', 2)),
    '0x48fa97aDb417367a480D6b93FBC26CB0B8E93F5a' : ('map', 1, ('loc', 3)),
    '0x48fa97aDb417367a480D6b93FBC26CB0B8E93F5a' : ('map', 1, ('loc', 4)),
    '0x48fa97aDb417367a480D6b93FBC26CB0B8E93F5a' : ('map', 1, ('loc', 5)),
    '0x48fa97aDb417367a480D6b93FBC26CB0B8E93F5a' : ('map', 1, ('loc', 6)),
    '0x48fa97aDb417367a480D6b93FBC26CB0B8E93F5a' : ('map', 1, ('loc', 7)),
    '0x48fa97aDb417367a480D6b93FBC26CB0B8E93F5a' : ('map', 1, ('loc', 8)),
    '0x48fa97aDb417367a480D6b93FBC26CB0B8E93F5a' : ('map', 1, ('loc', 9)),
    '0x48fa97aDb417367a480D6b93FBC26CB0B8E93F5a' : ('map', 1, ('loc', 10)),
    '0x48fa97aDb417367a480D6b93FBC26CB0B8E93F5a' : ('map', 1, ('loc', 11)),
    '0x48fa97aDb417367a480D6b93FBC26CB0B8E93F5a' : ('map', 1, ('loc', 12)),
    '0x48fa97aDb417367a480D6b93FBC26CB0B8E93F5a' : ('map', 1, ('loc', 13)),
    '0x48fa97aDb417367a480D6b93FBC26CB0B8E93F5a' : ('map', 1, ('loc', 14)),
    '0x48fa97aDb417367a480D6b93FBC26CB0B8E93F5a' : ('map', 1, ('loc', 15)),
    '0x48fa97aDb417367a480D6b93FBC26CB0B8E93F5a' : ('map', 1, ('loc', 16)),
    '0x48fa97aDb417367a480D6b93FBC26CB0B8E93F5a' : ('map', 1, ('loc', 17)),
    '0x48fa97aDb417367a480D6b93FBC26CB0B8E93F5a' : ('map', 1, ('loc', 18)),
    '0x48fa97aDb417367a480D6b93FBC26CB0B8E93F5a' : ('map', 1, ('loc', 19)),
}
