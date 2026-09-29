# Category map v2 for Aeneas icfp22 Hashmap.Properties.fst.
# Same as cats.py, but every P category is split into
#   P:<group>:refin  -- refinement lemmas: the statement says a GENERATED function
#                       (hash_map_*_fwd / hash_map_*_back from Hashmap.Funs) equals or
#                       refines a model function (a trusted view such as slot_t_find_s /
#                       hash_map_t_find_s / len_s, or a proof-internal model such as
#                       hash_map_insert_no_resize_s), plus their proofs and the one-line
#                       .fsti joins that restate them.
#   P:<group>:prop   -- everything else (model-level lemmas, invariant preservation,
#                       compositions "refinement + model lemma", list/arith helpers,
#                       and direct characterisations of generated functions that do not
#                       mention a model function -- see GEN_DIRECT).
# Pragma lines (#push-options/#pop-options/#restart-solver/#set-options) are re-tagged
# B:pragma, exactly as in cats.py, so ranges() never includes them.
#
# This file only GENERATES range lists; counting is done by hashmap-count.py.
#
# CLI:  python3 cats2.py PATTERN [--live|--dead] [--target view|model]
#   PATTERN without '*': exact category or prefix (as in cats.py), e.g. S:trust, P:ins
#   PATTERN with '*'   : fnmatch glob, e.g. 'P:*:refin', 'P:*:prop', 'S:int:*'
#   --live / --dead    : keep only lines outside / inside DEAD
#   --target view|model: keep only lines of REFIN entries with that target
import re, sys, fnmatch

F = '/home/charlielidbury/repos/ochre/competitors/aeneas-hashmap/icfp22/fstar/Hashmap.Properties.fst'
lines = open(F).read().split('\n')
N = 3247

spec = [
 ('B',1,37),
 ('P:gen:prop',38,83),
 ('S:int:remove',84,91),          # filter_one
 ('P:gen:prop',92,185),
 ('S:int:insert',186,199),        # find_update
 ('S:int:dead',200,205),          # pairwise_distinct
 ('S:trust',206,212),             # pairwise_rel
 ('P:gen:prop',213,222),          # flatten_append (dead)
 ('S:int:dead',223,228),          # fst_is_disctinct
 ('P:gen:prop',229,263),          # list_update lemmas
 ('S:trust',264,269),             # section header comments
 ('S:int:common',270,272),        # is_pos_usize, pos_usize
 ('S:trust',273,285),             # binding, slots_t, assoc_list, list_t_v
 ('S:int:common',286,289),        # list_t_len, list_t_index
 ('S:trust',290,290),             # slot_s
 ('S:int:common',291,292),        # slots_s
 ('S:int:dead',293,293),          # slot_t
 ('S:trust',294,295),             # slot_t_v
 ('S:int:common',296,303),        # slots_t_v, slots_t_al_v
 ('S:trust',304,309),             # hash_map_s
 ('S:int:common',310,314),        # hash_map_s_nes
 ('S:trust',315,322),             # hash_map_t_v, hash_map_t_al_v
 ('S:int:common',323,326),        # hash_map_t_nes
 ('S:trust',327,332),             # hash_key, hash_mod_key
 ('S:int:remove',333,333),        # not_same_key
 ('S:trust',334,355),             # same_key .. slot_t_find_s
 ('S:int:common',356,369),        # hash_map_s_find, hash_map_s_len
 ('S:trust',370,392),             # hash_map_t_find_s, slot_s_inv, slot_t_inv
 ('S:int:common',393,397),        # slots_s_inv
 ('S:trust',398,406),             # slots_t_inv
 ('S:int:common',407,411),        # hash_map_s_inv
 ('S:trust',412,434),             # hash_map_t_base_inv
 ('S:int:common',435,440),        # hash_map_t_same_params
 ('S:trust',441,464),             # hash_map_t_inv, len_s, find_s
 ('P:overload:prop',465,468),
 ('P:shared:prop',469,497),       # all-nil slot lemmas (new + clear)
 ('P:new:prop',498,619),          # allocate_slots (GEN_DIRECT), new_with_capacity, new
 ('P:clear:prop',620,698),        # clear_slots (GEN_DIRECT), clear
 ('P:len:refin',699,706),         # hash_map_len_fwd_lem (l = len_s self)
 ('P:ins:bucket:refin',707,751),  # insert_in_list_fwd_lem
 ('S:int:insert',752,763),        # hash_map_insert_in_list_s
 ('P:ins:bucket:refin',764,840),  # insert_in_list_back_lem_{append_s,update_s,s}
 ('P:ins:bucket:prop',841,1120),  # bucket invariants + compositions
 ('P:ins:noresize:refin',1121,1129),
 ('S:int:insert',1130,1150),      # insert_no_fail_s, insert_no_resize_s
 ('P:ins:noresize:refin',1151,1242), # insert_no_resize_fwd_back_lem_s
 ('S:int:insert',1243,1263),      # updated_binding, insert_post
 ('P:ins:noresize:prop',1264,1355),
 ('S:int:resize',1356,1384),      # result_hash_map_s_nes, move_elements_from_list_s
 ('P:ins:resize:refin',1385,1471),# move_elements_from_list_fwd_back_lem, move_elements_s_simpl (dead)
 ('S:int:resize',1472,1496),      # move_elements_s
 ('P:ins:resize:refin',1497,1601),# move_elements_fwd_back_lem_refin
 ('S:int:resize',1602,1623),      # move_elements_s_flat
 ('S:int:resize',1624,1638),      # flatten_i
 ('P:gen:prop',1639,1703),        # stray assert, flatten_i lemmas
 ('P:ins:resize:prop',1704,1725), # model-to-model: from_list_s_as_flat_lem
 ('S:int:resize',1726,1733),      # flat_comp
 ('P:ins:resize:prop',1734,1758), # model-to-model: flat_append_lem
 ('P:gen:prop',1759,1774),        # flatten_i_same_suffix
 ('P:ins:resize:prop',1775,1813), # model-to-model: s_lem_refin_flat
 ('S:int:resize',1814,1836),      # assoc_list_inv, disjoint_*, find_in_union
 ('P:shared:prop',1837,1848),     # for_all_binding_neq_find_lem
 ('P:ins:resize:prop',1849,1902),
 ('P:shared:prop',1903,1922),     # trivial invariant implications (dead)
 ('S:int:resize',1923,1929),      # partial_hash_map_s_inv
 ('P:ins:resize:prop',1930,2030),
 ('S:int:resize',2031,2046),      # hash_map_is_assoc_list, partial_hash_map_s_find
 ('P:ins:resize:prop',2047,2242), # incl. move_elements_fwd_back_lem (composition)
 ('S:int:resize',2243,2273),      # try_resize_s_simpl
 ('P:ins:resize:refin',2274,2302),# try_resize_fwd_back_lem_refin
 ('P:arith:prop',2303,2351),
 ('P:ins:loadfactor:prop',2352,2376),
 ('P:arith:prop',2377,2381),
 ('P:ins:loadfactor:prop',2382,2405),
 ('P:ins:resize:prop',2406,2485),
 ('S:int:resize',2486,2488),      # same_bindings
 ('P:ins:resize:prop',2489,2519), # try_resize_fwd_back_lem (composition)
 ('S:int:dead',2520,2533),        # hash_map_insert_s
 ('P:ins:top:refin',2534,2546),   # insert_fwd_back_lem_refin (dead)
 ('P:ins:top:prop',2547,2627),
 ('P:contains:refin',2628,2693),
 ('P:get:refin',2694,2760),
 ('P:getmut:refin',2761,2903),    # get_mut fwd (view) + get_mut_in_list_back + get_mut_back_lem_refin
 ('P:getmut:prop',2904,2937),     # get_mut_back_lem_aux (composition)
 ('P:remove:refin',2938,3022),    # remove fwd (view)
 ('S:int:remove',3023,3032),
 ('P:remove:refin',3033,3071),    # remove_from_list_back_lem_refin
 ('S:int:remove',3072,3081),
 ('P:remove:refin',3082,3163),    # remove_back_lem_refin
 ('P:remove:prop',3164,3247),
]

# Dead code, exactly as in the first census.
DEAD = [(213,221),(916,939),(1036,1060),(1302,1353),(1426,1470),(1639,1639),(1679,1702),
        (1903,1921),(2305,2307),(2313,2317),(2534,2545),
        (200,205),(223,228),(271,271),(287,288),(293,293),(2520,2533)]

# The refinement lemmas: (name, first line of val/let, last line of proof, target, live?)
# target: 'view'  = generated fn equals a trusted view function (len_s, slot_t_find_s, hash_map_t_find_s)
#         'model' = generated fn equals/refines a proof-internal model (hash_map_*_s, find_update, list append ...)
REFIN = [
 ('hash_map_len_fwd_lem (statement in .fsti 100-106)',  704,  704, 'view',  True),
 ('hash_map_insert_in_list_fwd_lem',                     712,  740, 'view',  True),
 ('hash_map_insert_in_list_back_lem_append_s',           765,  793, 'model', True),
 ('hash_map_insert_in_list_back_lem_update_s',           796,  824, 'model', True),
 ('hash_map_insert_in_list_back_lem_s',                  827,  839, 'model', True),
 ('hash_map_insert_no_resize_fwd_back_lem_s',           1153, 1241, 'model', True),
 ('hash_map_move_elements_from_list_fwd_back_lem',      1386, 1422, 'model', True),
 ('hash_map_move_elements_s_simpl (Pure-spec def)',     1444, 1470, 'model', False),
 ('hash_map_move_elements_fwd_back_lem_refin',          1497, 1599, 'model', True),
 ('hash_map_try_resize_fwd_back_lem_refin',             2287, 2301, 'model', True),
 ('hash_map_insert_fwd_back_lem_refin',                 2534, 2545, 'model', False),
 ('hash_map_contains_key_in_list_fwd_lem',              2632, 2657, 'view',  True),
 ('hash_map_contains_key_fwd_lem_aux + .fsti join',     2661, 2692, 'view',  True),
 ('hash_map_get_in_list_fwd_lem',                       2698, 2723, 'view',  True),
 ('hash_map_get_fwd_lem_aux + .fsti join',              2727, 2759, 'view',  True),
 ('hash_map_get_mut_in_list_fwd_lem',                   2766, 2791, 'view',  True),
 ('hash_map_get_mut_fwd_lem_aux + .fsti join',          2795, 2827, 'view',  True),
 ('hash_map_get_mut_in_list_back_lem',                  2833, 2859, 'model', True),
 ('hash_map_get_mut_back_lem_refin',                    2864, 2902, 'model', True),
 ('hash_map_remove_from_list_fwd_lem',                  2940, 2971, 'view',  True),
 ('hash_map_remove_fwd_lem_aux + .fsti join',           2973, 3021, 'view',  True),
 ('hash_map_remove_from_list_back_lem_refin',           3034, 3070, 'model', True),
 ('hash_map_remove_back_lem_refin',                     3083, 3162, 'model', True),
]

# Borderline, classified :prop -- direct pointwise characterisations of a generated
# function that mention no model function.
GEN_DIRECT = [('hash_map_allocate_slots_fwd_lem', 499, 537),
              ('hash_map_clear_slots_fwd_back_lem', 623, 659)]
# Borderline, classified :prop -- compositions whose ensures includes a refinement
# equation as one conjunct among properties (proof = refinement lemma + model lemma).
MIXED = [('hash_map_insert_in_list_back_lem_append (dead)', 919, 939),
         ('hash_map_insert_in_list_back_lem_update (dead)', 1039, 1060),
         ('hash_map_insert_in_list_back_lem', 1093, 1119),
         ('hash_map_move_elements_fwd_back_lem', 2162, 2241),
         ('hash_map_get_mut_back_lem_aux', 2905, 2934),
         ('hash_map_remove_back_lem_aux', 3221, 3243)]

cat = [None]*(N+1)
for c,a,b in spec:
    for i in range(a,b+1):
        assert cat[i] is None, (i,c,cat[i])
        cat[i] = c
_missing = [i for i in range(1,N+1) if cat[i] is None]
assert not _missing, _missing[:20]
for i in range(1,N+1):
    if re.match(r'^#(push-options|pop-options|restart-solver|set-options)', lines[i-1]):
        if cat[i] != 'B': cat[i] = 'B:pragma'
# every REFIN entry must lie inside a :refin category (pragmas aside)
for n,a,b,t,_ in REFIN:
    for i in range(a,b+1):
        assert cat[i].endswith(':refin') or cat[i].startswith('B'), (n,i,cat[i])

DEADSET = set(i for a,b in DEAD for i in range(a,b+1))

def _match(p, c):
    if '*' in p or '?' in p:
        return fnmatch.fnmatchcase(c, p)
    return c == p or c.startswith(p+':')

def ranges(pred):
    out=[]; start=None
    for i in range(1,N+2):
        ok = i<=N and pred(i)
        if ok and start is None: start=i
        if not ok and start is not None: out.append(f"{start}-{i-1}"); start=None
    return ' '.join(out)

if __name__=='__main__':
    args = sys.argv[1:]
    p = args[0]
    live = '--live' in args; dead = '--dead' in args
    target = args[args.index('--target')+1] if '--target' in args else None
    tset = None
    if target:
        tset = set(i for n,a,b,t,_ in REFIN if t==target for i in range(a,b+1))
    def pred(i):
        if not _match(p, cat[i]): return False
        if live and i in DEADSET: return False
        if dead and i not in DEADSET: return False
        if tset is not None and i not in tset: return False
        return True
    print(ranges(pred))
