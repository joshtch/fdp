import babel from 'rollup-plugin-babel';
import commonjs from 'rollup-plugin-commonjs';
import resolve from 'rollup-plugin-node-resolve';
//import { terser } from 'rollup-plugin-terser';

export default {
  input: 'src/fdp.js',
  plugins: [
    resolve(),
    commonjs({ include: 'node_modules/**' }),
    babel(),
//    terser({
//      sourcemap: true,
//      compress: {
//        pure_funcs: [
//            // fdlib
//            'domain_arr_max',
//            'domain_arrToStr',
//            'domain_str_decodeValue',
//            'domain_str_getValue',
//            'domain_bit_getValue',
//            'domain_sol_getValue',
//            'domain_num_createRange',
//            'domain_createEmpty',
//            'domain_createValue',
//            'domain_str_decodeValue',
//            'domain_toList',
//            'domain_max',
//            'domain_size',
//            'domain_min',
//            'domain_isSolved',
//            'domain_isZero',
//            'domain_hasNoZero',
//            'domain_hasZero',
//            'domain_isBool',
//            'domain_isBooly',
//            'domain_sharesNoElements',
//            'domain_createRange',
//            'domain_createRangeTrimmed',
//            'domain_toArr',
//            'domain_toStr',
//            'domain_toSmallest',
//            'domain_anyToSmallest',
//            'domain_arrToSmallest',
//            'domain_str_closeGaps',
//            'domain_containsValue',
//            'domain_num_containsValue',
//            'domain_createBoolyPair',
//            'domain__debug',
//            'domain_getFirstIntersectingValue',
//            'domain_getValue',
//            'domain_intersection',
//            'domain_intersectionValue',
//            'domain_isBoolyPair',
//            'domain_isEmpty',
//            'domain_numToStr',
//            'domain_removeGte',
//            'domain_removeGtUnsafe',
//            'domain_removeLte',
//            'domain_removeLtUnsafe',
//            'domain_removeValue',
//            'domain_resolveAsBooly',
//            'domain_str_encodeRange',
//            'domain_minus',
//            'domain_plus',
//            'INSPECT',
//            'getTerm',
//            'trie_create',
//            '_trie_debug',
//            'trie_get',
//            'trie_getNum',
//            'trie_getValueBitsize',
//            'trie_has',
//            'trie_hasNum',

//          // fdp-specific

//          // bounty
//          'bounty_getCounts',

//          // cutter
//          /* no pure functions in production */

//          // deduper
//          /* no pure functions in production */

//          // dsl2ml
//          /* no pure functions in production */

//          // minimizer
//          /* no pure functions in production */

//          // ml
//          'ml__debug',
//          'ml__opName',
//          'ml_countConstraints',
//          'ml_dec16',
//          'ml_dec32',
//          'ml_dec8',
//          'ml_getOpList',
//          'ml_getOpSizeSlow',
//          'ml_getRecycleOffset',
//          'ml_getRecycleOffsets',
//          'ml_hasConstraint',
//          'ml_recycleC3',
//          'ml_recycleVV',
//          'ml_sizeof',
//          'ml_validateSkeleton',

//          // ml2dsl
//          /* no pure functions in production */

//          // problem
//          /* no pure functions in production */

//          // fdp
//          /* no pure functions in production */

//          /* impure functions
//          // bounty
//          bounty_collect,    // 3rd arg modified
//          bounty_markVar,    // 1st arg modified
//          bounty_updateMeta, // 1st arg modified
//          bounty_getMeta,    // 1st arg modified
//          bounty_getOffset,  // 1st arg modified
//          bounty__debug,     // 1st arg modified
//          bounty__debugMeta, // 1st arg modified

//          // cutter
//          cutter, // 1st arg modified

//          // deduper
//          deduper, // throws error

//          // dsl2ml
//          dsl2ml, // 2nd arg modified

//          // minimizer
//          min_run, // throws
//          min_optimizeConstraints, // throws

//          // ml
//          ml_compileJumpAndConsolidate,
//          ml_compileJumpSafe,
//          ml_eliminate,
//          ml_enc16,
//          ml_enc32,
//          ml_enc8,
//          ml_walk,
//          ml_pump,
//          ml_recycles,
//          ml_stream,
//          ml_throw,
//          ml_any2c,
//          ml_any2cr,
//          ml_c2c2,
//          ml_c2vv,
//          ml_cr2c,
//          ml_cr2c2,
//          ml_cr2cr2,
//          ml_cr2vv,
//          ml_cr2vvv,
//          ml_cx2cx,
//          ml_vv2vv,
//          ml_vvv2c2,
//          ml_vvv2vv,
//          ml_vvv2vvv,
//          ml_heapSort16bitInline,
//          _ml_heapSort16bitInline,

//          // ml2dsl
//          ml2dsl, // throws
//          m2d__debug, // throws

//          // problem
//          problem_create, // throws
//          problem_from, // throws
//          */
//        ],
//        pure_getters: true,
//        unsafe: true,
//        unsafe_comps: false, // TODO: find out why things break when this is true
//        warnings: false,
//      },
//    }),
  ],
  external: ['fs', 'path', 'events', 'module', 'util', 'fdlib'],
  treeshake: {
    moduleSideEffects: false,
    propertyReadSideEffects: false,
  },
  output: [
    { file: 'dist/fdp.js', format: 'cjs', sourcemap: true },
    { file: 'dist/fdp.es.js', format: 'esm' },
  ],
};
