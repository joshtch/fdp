import { ASSERT, THROW, getTerm, TRACE, TRACE_SILENT, domain__debug, ASSERT_NORDOM, domain_getValue, domain_toArr, isTracing, setTracing, domain_isSolved, domain_isBoolyPair, TRACE_MORPH, domain_isBooly, domain_hasNoZero, domain_isBool, domain_isZero, domain_max, domain_size, domain_intersection, domain_createEmpty, domain_min, domain_createValue, domain_plus, domain_createRange, domain_removeValue, domain_intersectionValue, domain_removeGtUnsafe, EMPTY, domain_resolveAsBooly, domain_removeLte, domain_removeGte, domain_removeLtUnsafe, domain_hasZero, domain_arrToSmallest, domain_containsValue, SUB, SUP, $SOLVED, $REJECTED, $STABLE, $CHANGED, domain_minus, domain_divby, domain_mul, domain_invMul, domain_createBoolyPair, domain_sharesNoElements, trie_add, trie_create, trie_get, setTerm, INSPECT, domain_middleElement } from 'fdlib';

var ml_opcodeCounter = 0; // Note: all ops accept vars and literals
// - a var is signified by a V
// - an 8bit literal signified by 8
// - a 16bit literal signified by F

var ML_START = ml_opcodeCounter++;
var ML_ALL = ml_opcodeCounter++; // &     all()

var ML_DIFF = ml_opcodeCounter++; // !=    diff()

var ML_IMP = ml_opcodeCounter++; // ->                (logical implication)

var ML_LT = ml_opcodeCounter++; // <

var ML_LTE = ml_opcodeCounter++; // <=

var ML_NALL = ml_opcodeCounter++; // !&    nall()

var ML_NIMP = ml_opcodeCounter++; // !(->)

var ML_NONE = ml_opcodeCounter++; // ==0   none()

var ML_SAME = ml_opcodeCounter++; // ==    same()

var ML_SOME = ml_opcodeCounter++; // |     some()

var ML_XNOR = ml_opcodeCounter++; // !^    xnor()

var ML_XOR = ml_opcodeCounter++; // ^     xor()

var ML_ISALL = ml_opcodeCounter++;
var ML_ISDIFF = ml_opcodeCounter++;
var ML_ISLT = ml_opcodeCounter++;
var ML_ISLTE = ml_opcodeCounter++;
var ML_ISNALL = ml_opcodeCounter++;
var ML_ISNONE = ml_opcodeCounter++;
var ML_ISSAME = ml_opcodeCounter++;
var ML_ISSOME = ml_opcodeCounter++;
var ML_SUM = ml_opcodeCounter++;
var ML_PRODUCT = ml_opcodeCounter++;
var ML_MINUS = ml_opcodeCounter++;
var ML_DIV = ml_opcodeCounter++;
var ML_NOLEAF = ml_opcodeCounter++;
var ML_NOBOOL = ml_opcodeCounter++;
var ML_JMP = ml_opcodeCounter++;
var ML_JMP32 = ml_opcodeCounter++;
var ML_NOOP = ml_opcodeCounter++;
var ML_NOOP2 = ml_opcodeCounter++;
var ML_NOOP3 = ml_opcodeCounter++;
var ML_NOOP4 = ml_opcodeCounter++;
var ML_STOP = 0xff;
ASSERT(ml_opcodeCounter < 0xff, 'All opcodes are 8bit');
ASSERT(ML_START === 0);
ASSERT(ML_STOP === 0xff);
var SIZEOF_V = 1 + 2; // 16bit

var SIZEOF_W = 1 + 4; // 32bit
var SIZEOF_VVV = 1 + 2 + 2 + 2;
var SIZEOF_C = 1 + 2; // + 2*count

var SIZEOF_C_2 = SIZEOF_C + 2 * 2; // Fixed 2 var without result

var SIZEOF_CR_2 = SIZEOF_C + 2 * 2 + 2; // Fixed 2 var with result

var OFFSET_C_A = SIZEOF_C;
var OFFSET_C_B = SIZEOF_C + 2;
var OFFSET_C_C = SIZEOF_C + 4;
var OFFSET_C_R = OFFSET_C_C;

function ml_sizeof(ml, offset, op) {
  switch (op) {
    case ML_IMP:
    case ML_LT:
    case ML_LTE:
    case ML_NIMP:
    case ML_XOR:
      ASSERT(ml_dec16(ml, offset + 1) === 2);
      return SIZEOF_C_2;
    // Always

    case ML_START:
      return 1;

    case ML_ISLT:
    case ML_ISLTE:
    case ML_MINUS:
    case ML_DIV:
      return SIZEOF_VVV;

    case ML_ALL:
    case ML_DIFF:
    case ML_NALL:
    case ML_NONE:
    case ML_SAME:
    case ML_SOME:
    case ML_XNOR:
      if (ml && offset >= 0) return SIZEOF_C + _dec16(ml, offset + 1) * 2;
      return -1;

    case ML_ISALL:
    case ML_ISDIFF:
    case ML_ISNALL:
    case ML_ISNONE:
    case ML_ISSAME:
    case ML_ISSOME:
      if (ml && offset >= 0) return SIZEOF_C + _dec16(ml, offset + 1) * 2 + 2;
      ASSERT(false, 'dont allow this');
      return -1;

    case ML_SUM:
    case ML_PRODUCT:
      if (ml && offset >= 0) return SIZEOF_C + _dec16(ml, offset + 1) * 2 + 2;
      ASSERT(false, 'dont allow this');
      return -1;

    case ML_NOBOOL:
    case ML_NOLEAF:
      return SIZEOF_V;

    case ML_JMP:
      return SIZEOF_V + _dec16(ml, offset + 1);

    case ML_JMP32:
      return SIZEOF_W + _dec32(ml, offset + 1);

    case ML_NOOP:
      return 1;

    case ML_NOOP2:
      return 2;

    case ML_NOOP3:
      return 3;

    case ML_NOOP4:
      return 4;

    case ML_STOP:
      return 1;

    default:
      getTerm().log('(ml) unknown op', op, ' at', offset);
      TRACE('(ml_sizeof) unknown op: ' + ml[offset], ' at', offset);
      THROW('(ml_sizeof) unknown op: ' + ml[offset], ' at', offset);
  }
}

function _dec8(ml, pc) {
  return ml[pc];
}

function ml_dec8(ml, pc) {
  ASSERT(ml instanceof Uint8Array, 'ml should be Uint8Array');
  ASSERT(typeof pc === 'number' && pc >= 0 && pc < ml.length, 'Invalid or OOB', pc, '>=', ml.length);

  var num = _dec8(ml, pc);

  TRACE_SILENT(' . dec8pc decoding', num, 'from', pc);
  return num;
}

function _dec16(ml, pc) {
  return ml[pc++] << 8 | ml[pc];
}

function ml_dec16(ml, pc) {
  ASSERT(ml instanceof Uint8Array, 'ml should be Uint8Array');
  ASSERT(typeof pc === 'number' && pc >= 0 && pc < ml.length, 'Invalid or OOB', pc, '>=', ml.length);

  var n = _dec16(ml, pc);

  TRACE_SILENT(' . dec16pc decoding', ml[pc] << 8, 'from', pc, 'and', ml[pc + 1], 'from', pc + 1, '-->', n);
  return n;
}

function _dec32(ml, pc) {
  return ml[pc++] << 24 | ml[pc++] << 16 | ml[pc++] << 8 | ml[pc];
}

function ml_dec32(ml, pc) {
  ASSERT(ml instanceof Uint8Array, 'ml should be Uint8Array');
  ASSERT(typeof pc === 'number' && pc >= 0 && pc < ml.length, 'Invalid or OOB', pc, '>=', ml.length);

  var n = _dec32(ml, pc);

  TRACE_SILENT(' . dec32pc decoding', ml[pc], ml[pc + 1], ml[pc + 2], ml[pc + 3], '( x' + ml[pc].toString(16) + ml[pc + 1].toString(16) + ml[pc + 2].toString(16) + ml[pc + 3].toString(16), ') from', pc, '-->', n);
  return n;
}

function ml_enc8(ml, pc, num) {
  TRACE_SILENT(' . enc8(' + pc + ', ' + num + '/x' + (num && num.toString(16)) + ') at', pc, ' ');
  ASSERT(ml instanceof Uint8Array, 'ml should be Uint8Array');
  ASSERT(typeof pc === 'number' && pc >= 0 && pc < ml.length, 'Invalid or OOB', pc, '>=', ml.length);
  ASSERT(typeof num === 'number', 'Encoding numbers', num);
  ASSERT(num >= 0 && num <= 0xff, 'Only encode 8bit values', num, '0x' + num.toString(16));
  ASSERT(num >= 0, 'only expecting non-negative nums', num);
  ml[pc] = num;
}

function ml_enc16(ml, pc, num) {
  TRACE_SILENT(' - enc16(' + pc + ', ' + num + '/x' + num.toString(16) + ')', num >> 8 & 0xff, 'at', pc, 'and', num & 0xff, 'at', pc + 1);
  ASSERT(ml instanceof Uint8Array, 'ml should be Uint8Array');
  ASSERT(typeof pc === 'number' && pc >= 0 && pc < ml.length, 'Invalid or OOB', pc, '>=', ml.length);
  ASSERT(typeof num === 'number', 'Encoding numbers');
  ASSERT(num <= 0xffff, 'implement 32bit index support if this breaks', num);
  ASSERT(num >= 0, 'only expecting non-negative nums', num);
  ml[pc++] = num >> 8 & 0xff;
  ml[pc] = num & 0xff;
}

function ml_enc32(ml, pc, num) {
  TRACE_SILENT(' - enc32(' + pc + ', ' + num + '/x' + num.toString(16) + ')', ml[pc], ml[pc + 1], ml[pc + 2], ml[pc + 3], '( x' + ml[pc].toString(16) + ml[pc + 1].toString(16) + ml[pc + 2].toString(16) + ml[pc + 3].toString(16), ') at', pc + 1);
  ASSERT(ml instanceof Uint8Array, 'ml should be Uint8Array');
  ASSERT(typeof pc === 'number' && pc >= 0 && pc < ml.length, 'Invalid or OOB', pc, '>=', ml.length);
  ASSERT(typeof num === 'number', 'Encoding numbers');
  ASSERT(num <= 0xffffffff, 'implement 64bit index support if this breaks', num);
  ASSERT(num >= 0, 'only expecting non-negative nums', num);
  ml[pc++] = num >> 24 & 0xff;
  ml[pc++] = num >> 16 & 0xff;
  ml[pc++] = num >> 8 & 0xff;
  ml[pc] = num & 0xff;
}

function ml_eliminate(ml, offset, sizeof) {
  ASSERT(ml instanceof Uint8Array, 'ml should be Uint8Array', ml); // ASSERT(ml_validateSkeleton(ml, 'ml_eliminate; before'));

  TRACE(' - ml_eliminate: eliminating constraint at', offset, 'with size =', sizeof, ', ml=', ml.length < 50 ? ml.join(' ') : '<BIG>');
  ASSERT(typeof offset === 'number' && offset >= 0 && offset < ml.length, 'valid offset required');
  ASSERT(typeof sizeof === 'number' && sizeof >= 0, 'valid sizeof required');
  ASSERT(sizeof === ml_getOpSizeSlow(ml, offset), 'sizeof should match size of op at offset', sizeof, ml_getOpSizeSlow(ml, offset), ml__debug(ml, offset, 1, undefined, true, true)); // Maybe we should move to do this permanently "slow"

  ml_compileJumpSafe(ml, offset, sizeof);
  TRACE('    - after ml_eliminate:', ml.length < 50 ? ml.join(' ') : '<trunced>');
  ASSERT(ml_validateSkeleton(ml, 'ml_eliminate; after'));
}

function ml_compileJumpAndConsolidate(ml, offset, len) {
  TRACE('  - ml_jump: offset = ', offset, 'len = ', len);

  switch (ml[offset + len]) {
    case ML_NOOP:
      TRACE('  - jmp target is another jmp (noop), merging them');
      return ml_compileJumpAndConsolidate(ml, offset, len + 1);

    case ML_NOOP2:
      TRACE('  - jmp target is another jmp (noop2), merging them');
      return ml_compileJumpAndConsolidate(ml, offset, len + 2);

    case ML_NOOP3:
      TRACE('  - jmp target is another jmp (noop3), merging them');
      return ml_compileJumpAndConsolidate(ml, offset, len + 3);

    case ML_NOOP4:
      TRACE('  - jmp target is another jmp (noop4), merging them');
      return ml_compileJumpAndConsolidate(ml, offset, len + 4);

    case ML_JMP:
      var jmplen = ml_dec16(ml, offset + len + 1);
      ASSERT(jmplen > 0, 'dont think zero is a valid jmp len');
      ASSERT(jmplen <= 0xffff, 'oob');
      TRACE('  - jmp target is another jmp (len =', SIZEOF_V + jmplen, '), merging them');
      return ml_compileJumpAndConsolidate(ml, offset, len + SIZEOF_V + jmplen);

    case ML_JMP32:
      var jmplen32 = ml_dec32(ml, offset + len + 1);
      ASSERT(jmplen32 > 0, 'dont think zero is a valid jmp len');
      ASSERT(jmplen32 <= 0xffffffff, 'oob');
      TRACE('  - jmp target is a jmp32 (len =', SIZEOF_W + jmplen32, '), merging them');
      return ml_compileJumpAndConsolidate(ml, offset, len + SIZEOF_W + jmplen32);
  }

  ml_compileJumpSafe(ml, offset, len);
}

function ml_compileJumpSafe(ml, offset, len) {
  switch (len) {
    case 0:
      return THROW('this is a bug');

    case 1:
      TRACE('  - compiling a NOOP');
      return ml_enc8(ml, offset, ML_NOOP);

    case 2:
      TRACE('  - compiling a NOOP2');
      return ml_enc8(ml, offset, ML_NOOP2);

    case 3:
      TRACE('  - compiling a NOOP3');
      return ml_enc8(ml, offset, ML_NOOP3);

    case 4:
      TRACE('  - compiling a NOOP4');
      return ml_enc8(ml, offset, ML_NOOP4);

    default:
      if (len < 0xffff) {
        TRACE('  - compiling a ML_JMP of', len, '(compiles', len - SIZEOF_V, 'because SIZEOF_V=', SIZEOF_V, ')');
        ml_enc8(ml, offset, ML_JMP);
        ml_enc16(ml, offset + 1, len - SIZEOF_V);
      } else {
        TRACE('  - compiling a ML_JMP32 of', len, '(compiles', len - SIZEOF_W, 'because SIZEOF_W=', SIZEOF_W, ')');
        ml_enc8(ml, offset, ML_JMP32);
        ml_enc32(ml, offset + 1, len - SIZEOF_W);
      }

  } // ASSERT(ml_validateSkeleton(ml, 'ml_jump; after'));

}

function ml_countConstraints(ml) {
  var pc = 0;
  var constraints = 0;

  while (pc < ml.length) {
    var pcStart = pc;
    var op = ml[pc];

    switch (op) {
      case ML_START:
        if (pc !== 0) return THROW('mlConstraints: zero op @', pcStart, 'Uint8Array(' + ml.toString('hex').replace(/(..)/g, '$1 ') + ')');
        ++pc;
        break;

      case ML_STOP:
        return constraints;

      case ML_NOOP:
        ++pc;
        break;

      case ML_NOOP2:
        pc += 2;
        break;

      case ML_NOOP3:
        pc += 3;
        break;

      case ML_NOOP4:
        pc += 4;
        break;

      case ML_JMP:
        pc += SIZEOF_V + _dec16(ml, pc + 1);
        break;

      case ML_JMP32:
        pc += SIZEOF_W + _dec32(ml, pc + 1);
        break;

      default:
        var size = ml_sizeof(ml, pc, op); // Throws if op is unknown

        ++constraints;
        pc += size;
    }
  }

  THROW('ML OOB');
}

function ml_hasConstraint(ml) {
  // Technically this should be cheap; either the first
  // op is a constraint or it's a jump directly to stop.
  // (all jumps should be consolidated)
  var pc = 0;

  while (pc < ml.length) {
    switch (ml[pc]) {
      case ML_START:
        if (pc !== 0) return ml_throw('oops');
        ++pc;
        break;

      case ML_STOP:
        return false;

      case ML_NOOP:
        ++pc;
        break;

      case ML_NOOP2:
        pc += 2;
        break;

      case ML_NOOP3:
        pc += 3;
        break;

      case ML_NOOP4:
        pc += 4;
        break;

      case ML_JMP:
        pc += SIZEOF_V + _dec16(ml, pc + 1);
        break;

      case ML_JMP32:
        pc += SIZEOF_W + _dec32(ml, pc + 1);
        break;

      default:
        return true;
    }
  }

  THROW('ML OOB');
}

function ml_c2c2(ml, offset, argCount, opCode, indexA, indexB) {
  // "count without result" (diff, some, nall, etc) to same count type with 2 args without result
  TRACE(' -| ml_c2c2 | from', offset, ', argCount=', argCount, 'to op', ml__opName(opCode), ', args:', indexA, indexB);
  ASSERT(ml_getOpSizeSlow(ml, offset) >= SIZEOF_C_2, 'the c2 should fit the existing space entirely');
  ASSERT(ml_dec16(ml, offset + 1) === argCount, 'argcount should match');
  ASSERT(argCount > 1, 'this fails with count<2 because theres not enough space'); // ASSERT(ml_validateSkeleton(ml, 'ml_c2c2-before'));

  ml_enc8(ml, offset, opCode);
  ml_enc16(ml, offset + 1, 2);
  ml_enc16(ml, offset + OFFSET_C_A, indexA);
  ml_enc16(ml, offset + OFFSET_C_B, indexB);
  var oldLen = SIZEOF_C + argCount * 2;
  if (SIZEOF_C_2 < oldLen) ml_compileJumpSafe(ml, offset + SIZEOF_C_2, oldLen - SIZEOF_C_2);
  ASSERT(ml_validateSkeleton(ml, 'ml_c2c2'));
}

function ml_cx2cx(ml, offset, argCount, opCode, args) {
  TRACE(' -| ml_cx2cx | from', offset, 'was argCount=', argCount, 'to op', ml__opName(opCode), 'with args', args, ', new size should be', SIZEOF_C + args.length * 2);
  ASSERT(ml instanceof Uint8Array, 'ml is Uint8Array');
  ASSERT(typeof offset === 'number' && offset > 0 && offset < ml.length, 'valid offset', offset);
  ASSERT(typeof argCount === 'number' && argCount > 0 && argCount < ml.length, 'valid argCount', argCount);
  ASSERT(Array.isArray(args), 'args is list of indexes', args);
  ASSERT(argCount === args.length, 'this function excepts to morph one count op into another count op of the same size', argCount, args.length, args);
  args.sort(function (a, b) {
    return a - b;
  }); // Compile args sorted

  var opSize = SIZEOF_C + argCount * 2;
  ASSERT(argCount === args.length === (ml_getOpSizeSlow(ml, offset) === opSize), 'if same argcount then same size');
  ASSERT(ml_getOpSizeSlow(ml, offset) === opSize, 'the should fit the existing space entirely');
  ml_enc8(ml, offset, opCode);
  ml_enc16(ml, offset + 1, argCount);

  for (var i = 0; i < argCount; ++i) {
    ml_enc16(ml, offset + SIZEOF_C + i * 2, args[i]);
  }

  ASSERT(ml_validateSkeleton(ml, 'ml_cx2cx'));
}

function ml_any2c(ml, offset, oldSizeof, opCode, args) {
  TRACE(' -| ml_any2c | from', offset, 'was len=', oldSizeof, 'to op', ml__opName(opCode), 'with args', args, ', new size should be', SIZEOF_C + args.length * 2);
  ASSERT(ml instanceof Uint8Array, 'ml is Uint8Array');
  ASSERT(typeof offset === 'number' && offset > 0 && offset < ml.length, 'valid offset', offset);
  ASSERT(typeof oldSizeof === 'number' && offset > 0 && offset < ml.length, 'valid oldSizeof', oldSizeof);
  ASSERT(Array.isArray(args), 'args is list of indexes', args);
  var count = args.length;
  var opSize = SIZEOF_C + count * 2;
  ASSERT(ml_getOpSizeSlow(ml, offset) >= opSize, 'the c2 should fit the existing space entirely');
  ml_enc8(ml, offset, opCode);
  ml_enc16(ml, offset + 1, count);

  for (var i = 0; i < count; ++i) {
    ml_enc16(ml, offset + SIZEOF_C + i * 2, args[i]);
  }

  if (opSize < oldSizeof) ml_compileJumpSafe(ml, offset + opSize, oldSizeof - opSize);
  ASSERT(ml_validateSkeleton(ml, 'ml_any2c'));
}

function ml_cr2cr2(ml, offset, argCount, opCode, indexA, indexB, indexC) {
  // "count with result and any args to count with result with 2 args"
  TRACE(' -| ml_cr2cr2 | from', offset, ', argCount=', argCount, 'to op', ml__opName(opCode), 'with args:', indexA, indexB, indexC);
  ASSERT(argCount >= 2, 'if this is called for count ops with 1 or 0 args then we have a problem... a cr[' + argCount + '] wont fit that');
  ASSERT(ml instanceof Uint8Array, 'ml is Uint8Array');
  ASSERT(typeof offset === 'number' && offset > 0 && offset < ml.length, 'valid offset', offset);
  ASSERT(typeof opCode === 'number' && offset >= 0, 'valid opCode', opCode);
  ASSERT(typeof indexA === 'number' && indexA >= 0, 'valid indexA', indexA);
  ASSERT(typeof indexB === 'number' && indexB >= 0, 'valid indexB', indexB);
  ASSERT(typeof indexC === 'number' && indexC >= 0, 'valid indexC', indexC);
  ASSERT(ml_getOpSizeSlow(ml, offset) >= SIZEOF_CR_2, 'the cr2 should fit the existing space entirely');
  ml_enc8(ml, offset, opCode);
  ml_enc16(ml, offset + 1, 2); // Arg count

  ml_enc16(ml, offset + OFFSET_C_A, indexA);
  ml_enc16(ml, offset + OFFSET_C_B, indexB);
  ml_enc16(ml, offset + OFFSET_C_C, indexC);
  var oldLen = SIZEOF_C + argCount * 2 + 2;
  if (SIZEOF_CR_2 < oldLen) ml_compileJumpSafe(ml, offset + SIZEOF_CR_2, oldLen - SIZEOF_CR_2);
  ASSERT(ml_validateSkeleton(ml, 'ml_cr2cr2'));
}

function ml_cr2c2(ml, offset, argCount, opCode, indexA, indexB) {
  // "count with result"
  var oldArgCount = ml_dec16(ml, offset + 1);
  TRACE(' -| ml_cr2c2 | from', offset, ', with argCount=', oldArgCount, ' and a result var, to a argCount=', argCount, ' without result, op', ml__opName(opCode), ', args:', indexA, indexB); // Count with result and any args to count with result and (exactly) 2 args

  ASSERT(argCount >= 1, 'if this is called for count ops with 0 args then we have a problem... a c[' + argCount + '] wont fit that');
  ASSERT(ml instanceof Uint8Array, 'ml is Uint8Array');
  ASSERT(typeof offset === 'number' && offset > 0 && offset < ml.length, 'valid offset', offset);
  ASSERT(typeof opCode === 'number' && offset >= 0, 'valid opCode', opCode);
  ASSERT(typeof indexA === 'number' && indexA >= 0, 'valid indexA', indexA);
  ASSERT(typeof indexB === 'number' && indexB >= 0, 'valid indexB', indexB);
  ASSERT(ml_getOpSizeSlow(ml, offset) >= SIZEOF_C_2, 'the c2 should fit the existing space entirely');
  ml_enc8(ml, offset, opCode);
  ml_enc16(ml, offset + 1, 2); // Arg count

  ml_enc16(ml, offset + OFFSET_C_A, indexA);
  ml_enc16(ml, offset + OFFSET_C_B, indexB);
  var oldLen = SIZEOF_C + oldArgCount * 2 + 2;
  if (SIZEOF_C_2 < oldLen) ml_compileJumpSafe(ml, offset + SIZEOF_C_2, oldLen - SIZEOF_C_2);
  ASSERT(ml_validateSkeleton(ml, 'ml_cr2c2'));
}

function ml_cr2c(ml, offset, oldArgCount, opCode, args) {
  // "count with result to count"
  // count with result and any args to count without result and any args
  // not "any" because the number of new args can at most be only be one more than the old arg count
  TRACE(' -| ml_cr2c | from', offset, ', with oldArgCount=', oldArgCount, ' and a result var, to a oldArgCount=', oldArgCount, ' without result, op', ml__opName(opCode), ', args:', args);
  ASSERT(ml instanceof Uint8Array, 'ml is Uint8Array');
  ASSERT(typeof offset === 'number' && offset > 0 && offset < ml.length, 'valid offset', offset);
  ASSERT(typeof oldArgCount === 'number', 'valid oldArgCount', oldArgCount);
  ASSERT(typeof opCode === 'number' && offset >= 0, 'valid opCode', opCode);
  ASSERT(Array.isArray(args) && args.every(function (v) {
    return typeof v === 'number' && v >= 0;
  }));
  ASSERT(oldArgCount + 1 >= args.length, 'cr can holds one index more than c so we can compile one more arg here', oldArgCount, '->', args.length);
  var newArgCount = args.length;
  ml_enc8(ml, offset, opCode);
  ml_enc16(ml, offset + 1, newArgCount);

  for (var i = 0; i < newArgCount; ++i) {
    ml_enc16(ml, offset + SIZEOF_C + i * 2, args[i]);
  }

  var oldLen = SIZEOF_C + oldArgCount * 2 + 2;
  var newLen = SIZEOF_C + newArgCount * 2;
  if (newLen < oldLen) ml_compileJumpSafe(ml, offset + newLen, oldLen - newLen);
  ASSERT(ml_validateSkeleton(ml, 'ml_cr2c'));
}

function ml_vvv2c2(ml, offset, opCode, indexA, indexB) {
  TRACE(' -| ml_vvv2c2 |', 'to op', ml__opName(opCode), ', args:', indexA, indexB);
  ASSERT(ml instanceof Uint8Array, 'ml is Uint8Array');
  ASSERT(typeof offset === 'number' && offset > 0 && offset < ml.length, 'valid offset', offset);
  ASSERT(typeof opCode === 'number' && offset >= 0, 'valid opCode', opCode);
  ASSERT(typeof indexA === 'number' && indexA >= 0, 'valid indexA', indexA);
  ASSERT(typeof indexB === 'number' && indexB >= 0, 'valid indexB', indexB);
  ASSERT(ml_getOpSizeSlow(ml, offset) === SIZEOF_C_2, 'the existing space should be a vvv and that should be a c2');
  ASSERT(SIZEOF_VVV === SIZEOF_C_2, 'need to check here if this changes'); // Note: size(vvv) is same as size(c2)

  ml_enc8(ml, offset, opCode);
  ml_enc16(ml, offset + 1, 2);
  ml_enc16(ml, offset + OFFSET_C_A, indexA);
  ml_enc16(ml, offset + OFFSET_C_B, indexB);
  ASSERT(ml_validateSkeleton(ml, 'ml_vvv2c2'));
}

function ml_walk(ml, offset, callback) {
  ASSERT(ml instanceof Uint8Array, 'ml is Uint8Array');
  ASSERT(typeof offset === 'number' && offset >= 0 && offset < ml.length, 'offset should be valid and not oob');
  ASSERT(typeof callback === 'function', 'callback should be callable');
  var len = ml.length;
  var op = ml[offset];

  while (offset < len) {
    op = ml[offset];

    if (process.env.NODE_ENV !== 'production') {
      if (offset !== 0 && op === ML_START) {
        ml_throw(ml, offset, 'should not see op=0 unless offset=0');
      }
    }

    var sizeof = ml_sizeof(ml, offset, op);
    ASSERT(sizeof > 0, 'ops should occupy space');
    var r = callback(ml, offset, op, sizeof);
    if (r !== undefined) return r;
    offset += sizeof;
  }
}

function ml_validateSkeleton(ml, msg) {
  if (process.env.NODE_ENV !== 'production') {
    TRACE_SILENT('--- ml_validateSkeleton', msg);
    var started = false;
    var stopped = false;
    ml_walk(ml, 0, function (ml, offset, op) {
      if (op === ML_START && offset === 0) started = true;
      if (op === ML_START && offset !== 0) ml_throw(ml, offset, 'ml_validateSkeleton: Found ML_START at offset');
      if (op === ML_STOP) stopped = true;else if (stopped) ml_throw(ml, offset, 'ml_validateSkeleton: Should stop after encountering a stop but did not');
    });
    if (!started || !stopped) ml_throw(ml, ml.length, 'ml_validateSkeleton: Missing a ML_START or ML_STOP');
    TRACE_SILENT('--- PASS ml_validateSkeleton');
    return true;
  }
}

function ml_getRecycleOffsets(ml, fromOffset, slotCount, sizePerSlot) {
  TRACE(' - ml_getRecycleOffsets looking for empty spaces to fill', slotCount, 'times', sizePerSlot, 'bytes');
  ASSERT(typeof fromOffset === 'number' && fromOffset >= 0, 'expecting fromOffset', fromOffset);
  ASSERT(typeof slotCount === 'number' && slotCount > 0, 'expecting slotCount', slotCount);
  ASSERT(typeof sizePerSlot === 'number' && sizePerSlot > 0, 'expecting sizePerSlot', sizePerSlot);
  var spaces = []; // Find a jump which covers at least the requiredSize

  ml_walk(ml, fromOffset, function (ml, offset, op) {
    TRACE('   - considering op', op, 'at', offset);

    if (op === ML_JMP || op === ML_JMP32) {
      var size = ml_getOpSizeSlow(ml, offset);
      TRACE('   - found jump of', size, 'bytes at', offset + ', wanted', sizePerSlot, sizePerSlot <= size ? ' so is ok!' : ' so is too small');

      if (size >= sizePerSlot) {
        spaces.push(offset); // Only add it once!

        do {
          // Remove as many from count as there fit in this empty space
          --slotCount;
          size -= sizePerSlot;
        } while (slotCount && size >= sizePerSlot);

        if (!slotCount) return true;
      }
    }
  });
  if (slotCount) return false; // Unable to collect enough spaces

  return spaces;
}

function ml_recycles(ml, bins, loops, sizeofOp, callback) {
  var i = 0;

  while (i < loops) {
    var currentRecycleOffset = bins.pop();
    ASSERT(ml_dec8(ml, currentRecycleOffset) === ML_JMP, 'should only get jumps here'); // Might trap a case where we clobber

    var sizeLeft = ml_getOpSizeSlow(ml, currentRecycleOffset);
    ASSERT(sizeLeft >= sizeofOp, 'this is what should have been asked for when getting recycled spaces');

    do {
      var stop = callback(currentRecycleOffset, i, sizeLeft);
      if (stop) return;
      ++i;
      sizeLeft -= sizeofOp;
      currentRecycleOffset += sizeofOp;
    } while (sizeLeft >= sizeofOp && i < loops);

    if (sizeLeft) ml_compileJumpSafe(ml, currentRecycleOffset, sizeLeft);
    ASSERT(ml_validateSkeleton(ml), 'ml_recycles'); // Cant check earlier
  }
}

function ml_getOpSizeSlow(ml, offset) {
  ASSERT(ml instanceof Uint8Array, 'ml is Uint8Array');
  ASSERT(typeof offset === 'number' && offset >= 0 && offset < ml.length, 'ml_getOpSizeSlow OOB'); // This is much slower compared to using the constants because it has to read from the ML
  // this function exists to suplement recycling, where you must read the size of the jump
  // otherwise you won't know how much space is left after recycling

  var size = ml_sizeof(ml, offset, ml[offset]);
  TRACE_SILENT(' - ml_getOpSizeSlow', offset, ml.length, '-->', size);
  return size;
}

function ml__debug(ml, offset, max, problem, mlAlways, _from_ml_throw) {
  var getDomain = problem && problem.getDomain;
  var names = problem && problem.varNames;

  function ml_index(offset) {
    var index = _dec16(ml, offset);

    return '{index=' + index + (problem && index < names.length ? ',name=' + names[index] : '') + (problem ? ',' + domain__debug(getDomain(index)) : '') + '}';
  }

  function ml_16(offset) {
    return _dec16(ml, offset);
  }

  var AB; // Grrr switches and let are annoying

  var rv = [];
  if (max < 0) max = ml.length;
  var pc = offset;
  var count = 0;

  while (count++ < max && pc < ml.length) {
    var name = '';
    var op = ml[pc]; // Should have an option to allow it when explicitly stated like below...

    /* eslint-disable no-fallthrough */

    switch (op) {
      case ML_START:
        if (pc !== 0) {
          TRACE('collected debugs up to error:', rv);
          if (!_from_ml_throw) ml_throw(ml, pc, 'ML_START at non-zero');
          rv.push('unused_error(0)');
          return rv.join('\n');
        }

        break;

      case ML_IMP:
        if (!name) name = '->';

      /* Fall-through */

      case ML_NIMP:
        if (!name) name = '!->';

      /* Fall-through */

      case ML_LT:
        if (!name) name = '<';

      /* Fall-through */

      case ML_LTE:
        if (!name) name = '<=';

      /* Fall-through */

      case ML_XOR:
        if (!name) name = '^';
        rv.push(ml_index(pc + OFFSET_C_A) + ' ' + name + ' ' + ml_index(pc + OFFSET_C_B));
        break;

      case ML_ISLT:
        if (!name) name = '<?';

      /* Fall-through */

      case ML_ISLTE:
        if (!name) name = '<=?';
        AB = ml_index(pc + 1) + ' ' + name + ' ' + ml_index(pc + 3);
        rv.push(ml_index(pc + 5) + ' = ' + AB);
        break;

      case ML_SUM:
        if (!name) name = 'sum';

      /* Fall-through */

      case ML_PRODUCT:
        if (!name) name = 'product';

      /* Fall-through */

      case ML_ISALL:
        if (!name) name = 'isall';

      /* Fall-through */

      case ML_ISDIFF:
        if (!name) name = 'isdiff';

      /* Fall-through */

      case ML_ISNALL:
        if (!name) name = 'isnall';

      /* Fall-through */

      case ML_ISSAME:
        if (!name) name = 'issame';

      /* Fall-through */

      case ML_ISSOME:
        if (!name) name = 'issome';

      /* Fall-through */

      case ML_ISNONE:
        if (!name) name = 'isnone';
        var vars = '';
        var varcount = ml_16(pc + 1);

        for (var i = 0; i < varcount; ++i) {
          vars += ml_index(pc + SIZEOF_C + i * 2) + ' ';
        }

        vars = name + '(' + vars + ')';
        vars = ml_index(pc + SIZEOF_C + varcount * 2) + ' = ' + vars;
        rv.push(vars);
        break;

      case ML_ALL:
        if (!name) name = 'all';

      /* Fall-through */

      case ML_NALL:
        if (!name) name = 'nall';

      /* Fall-through */

      case ML_SAME:
        if (!name) name = 'same';

      /* Fall-through */

      case ML_SOME:
        if (!name) name = 'some';

      /* Fall-through */

      case ML_NONE:
        if (!name) name = 'none';

      /* Fall-through */

      case ML_XNOR:
        if (!name) name = 'xnor';

      /* Fall-through */

      case ML_DIFF:
        if (!name) name = 'diff';
        var xvars = '';
        var xvarcount = ml_16(pc + 1);

        for (var _i = 0; _i < xvarcount; ++_i) {
          xvars += ml_index(pc + SIZEOF_C + _i * 2) + ' ';
        }

        xvars = name + '(' + xvars + ')';
        rv.push(xvars);
        break;

      case ML_MINUS:
        if (!name) name = '-';

      /* Fall-through */

      case ML_DIV:
        if (!name) name = '/';
        AB = ml_index(pc + 1) + ' ' + name + ' ' + ml_index(pc + 3);
        rv.push(ml_index(pc + 5) + ' = ' + AB);
        break;

      case ML_JMP:
        rv.push('jmp(' + _dec16(ml, pc + 1) + ')');
        break;

      case ML_JMP32:
        rv.push('jmp32(' + _dec32(ml, pc + 1) + ')');
        break;

      case ML_NOBOOL:
        rv.push('nobool(' + _dec16(ml, pc + 1) + ')');
        break;

      case ML_NOLEAF:
        rv.push('noleaf(' + _dec16(ml, pc + 1) + ')');
        break;

      case ML_NOOP:
        rv.push('noop(1)');
        break;

      case ML_NOOP2:
        rv.push('noop(2)');
        break;

      case ML_NOOP3:
        rv.push('noop(3)');
        break;

      case ML_NOOP4:
        rv.push('noop(4)');
        break;

      case ML_STOP:
        rv.push('stop()');
        break;

      default:
        THROW('add me [pc=' + pc + ', op=' + ml[pc] + ']');
    }

    var size = ml_sizeof(ml, pc, op); // GetTerm().log('size was:', size, 'rv=', rv);

    if (max !== 1 || mlAlways) rv.push("\x1B[90m" + size + 'b (' + pc + ' ~ ' + (pc + size) + ') -> 0x   ' + [].concat(ml.slice(pc, pc + Math.min(size, 100))).map(function (c) {
      return (c < 16 ? '0' : '') + c.toString(16);
    }).join(' ') + (size > 100 ? '... (trunced)' : '') + "\x1B[0m");
    pc += size;
  }

  return max === 1 ? rv.join('\n') : ' ## ML Debug:\n' + rv.join('\n') + '\n ## End of ML Debug' + (offset || pc < ml.length ? offset ? ' (did not start at begin of ml!)' : ' (did not list all ops, ml at ' + pc + ' / ' + ml.length + '))...' : '') + '\n';
}

function ml__opName(op) {
  ASSERT(typeof op === 'number', 'op should be a constant number');

  switch (op) {
    case ML_ALL:
      return 'ML_ALL';

    case ML_START:
      return 'ML_START';

    case ML_SAME:
      return 'ML_SAME';

    case ML_LT:
      return 'ML_LT';

    case ML_LTE:
      return 'ML_LTE';

    case ML_XOR:
      return 'ML_XOR';

    case ML_XNOR:
      return 'ML_XNOR';

    case ML_IMP:
      return 'ML_IMP';

    case ML_NIMP:
      return 'ML_NIMP';

    case ML_ISSAME:
      return 'ML_ISSAME';

    case ML_ISDIFF:
      return 'ML_ISDIFF';

    case ML_ISLT:
      return 'ML_ISLT';

    case ML_ISLTE:
      return 'ML_ISLTE';

    case ML_SUM:
      return 'ML_SUM';

    case ML_PRODUCT:
      return 'ML_PRODUCT';

    case ML_ISALL:
      return 'ML_ISALL';

    case ML_ISNALL:
      return 'ML_ISNALL';

    case ML_ISSOME:
      return 'ML_ISSOME';

    case ML_ISNONE:
      return 'ML_ISNONE';

    case ML_NALL:
      return 'ML_NALL';

    case ML_SOME:
      return 'ML_SOME';

    case ML_NONE:
      return 'ML_NONE';

    case ML_DIFF:
      return 'ML_DISTINCT';

    case ML_MINUS:
      return 'ML_MINUS';

    case ML_DIV:
      return 'ML_DIV';

    case ML_NOBOOL:
      return 'ML_NOBOOL';

    case ML_NOLEAF:
      return 'ML_NOLEAF';

    case ML_JMP:
      return 'ML_JMP';

    case ML_JMP32:
      return 'ML_JMP32';

    case ML_NOOP:
      return 'ML_NOOP';

    case ML_NOOP2:
      return 'ML_NOOP2';

    case ML_NOOP3:
      return 'ML_NOOP3';

    case ML_NOOP4:
      return 'ML_NOOP4';

    case ML_STOP:
      return 'ML_STOP';

    default:
      THROW('[ML] unknown op, fixme [' + op + ']');
  }
}

function ml_throw(ml, offset, msg) {
  var term = getTerm();
  term.error('\nThere was an ML related error;', msg);
  var before = ml.slice(Math.max(0, offset - 30), offset);
  var after = ml.slice(offset, offset + 20);
  term.error('ML at error (offset=' + offset + '/' + ml.length + '):', before, after);
  term.error('->', ml__debug(ml, offset, 1, undefined, true, true));
  THROW(msg);
}

function ml_getOpList(ml) {
  var pc = 0;
  var rv = [];

  while (pc < ml.length) {
    var op = ml[pc];

    switch (op) {
      case ML_START:
        if (pc !== 0) {
          rv.push('error(0)');
          return rv.join(',');
        }

        break;

      case ML_SAME:
        rv.push('same');
        break;

      case ML_LT:
        rv.push('lt');
        break;

      case ML_LTE:
        rv.push('lte');
        break;

      case ML_ALL:
        rv.push('all');
        break;

      case ML_NONE:
        rv.push('none');
        break;

      case ML_XOR:
        rv.push('xor');
        break;

      case ML_XNOR:
        rv.push('xnor');
        break;

      case ML_IMP:
        rv.push('imp');
        break;

      case ML_NIMP:
        rv.push('nimp');
        break;

      case ML_ISLT:
        rv.push('islt');
        break;

      case ML_ISLTE:
        rv.push('islte');
        break;

      case ML_SUM:
        rv.push('sum');
        break;

      case ML_PRODUCT:
        rv.push('product');
        break;

      case ML_ISALL:
        rv.push('isall');
        break;

      case ML_ISDIFF:
        rv.push('isdiff');
        break;

      case ML_ISNALL:
        rv.push('isnall');
        break;

      case ML_ISNONE:
        rv.push('isnone');
        break;

      case ML_ISSAME:
        rv.push('issame');
        break;

      case ML_ISSOME:
        rv.push('issome');
        break;

      case ML_NALL:
        rv.push('nall');
        break;

      case ML_SOME:
        rv.push('some');
        break;

      case ML_DIFF:
        rv.push('diff');
        break;

      case ML_MINUS:
        rv.push('minus');
        break;

      case ML_DIV:
        rv.push('div');
        break;

      case ML_NOBOOL:
      case ML_NOLEAF:
      case ML_JMP:
      case ML_JMP32:
      case ML_NOOP:
      case ML_NOOP2:
      case ML_NOOP3:
      case ML_NOOP4:
      case ML_STOP:
        break;

      default:
        rv.push('??!??');
    }

    pc += ml_sizeof(ml, pc, op);
  }

  return rv.sort(function (a, b) {
    return a < b ? -1 : 1;
  }).join(',');
}

function ml_heapSort16bitInline(ml, offset, argCount) {
  _ml_heapSort16bitInline(ml, offset, argCount); // TRACE('     - op now:', ml__debug(ml, offset-SIZEOF_C, 1))


  TRACE('     ### </ml_heapSort16bitInline> values after:', new Array(argCount).fill(0).map(function (_, i) {
    return _dec16(ml, offset + i * 2);
  }).join(' '), 'buf:', ml.slice(offset, offset + argCount * 2).join(' '));
  ASSERT(ml_validateSkeleton(ml, 'ml_heapSort16bitInline'));
}

function _ml_heapSort16bitInline(ml, offset, argCount) {
  ASSERT(ml instanceof Uint8Array, 'ml is Uint8Array');
  ASSERT(typeof offset === 'number' && (offset === 0 || offset > 0 && offset < ml.length), 'valid offset', ml.length, offset, argCount);
  ASSERT(typeof argCount === 'number' && (argCount === 0 || argCount > 0 && offset + argCount * 2 <= ml.length), 'valid count', ml.length, offset, argCount);
  TRACE('     ### <ml_heapSort16bitInline>, argCount=', argCount, ', offset=', offset, ', buf=', ml.slice(offset, offset + argCount * 2));
  TRACE('     - values before:', new Array(argCount).fill(0).map(function (_, i) {
    return _dec16(ml, offset + i * 2);
  }).join(' '));

  if (argCount <= 1) {
    TRACE(' - (argCount <= 1 so finished)');
    return;
  }

  ml_heapify(ml, offset, argCount);
  var end = argCount - 1;

  while (end > 0) {
    TRACE('     - swapping first elemement (should be biggest of values left to do) [', _dec16(ml, offset), '] with last [', _dec16(ml, offset + end * 2), '] and reducing end [', end, '->', end - 1, ']');
    ml_swap16(ml, offset, offset + end * 2);
    TRACE('     - (total) buffer now: Uint8Array(', [].map.call(ml.slice(offset, offset + argCount * 2), function (b) {
      return (b < 16 ? '0' : '') + b.toString(16);
    }).join(' '), ')');
    --end;
    ml_heapRepair(ml, offset, 0, end);
  }
}

function ml_heapParent(index) {
  return Math.floor((index - 1) / 2);
}

function ml_heapLeft(index) {
  return index * 2 + 1;
}

function ml_heapRight(index) {
  return index * 2 + 2;
}

function ml_heapify(ml, offset, len) {
  TRACE('     - ml_heapify', ml.slice(offset, offset + len * 2), offset, len);
  var start = ml_heapParent(len - 1);

  while (start >= 0) {
    ml_heapRepair(ml, offset, start, len - 1);
    --start; // Wont this cause it to do it redundantly twice?
  }

  TRACE('     - ml_heapify end');
}

function ml_heapRepair(ml, offset, startIndex, endIndex) {
  TRACE('     - ml_heapRepair', offset, startIndex, endIndex, 'Uint8Array(', [].map.call(ml.slice(offset + startIndex * 2, offset + startIndex * 2 + (endIndex - startIndex + 1) * 2), function (b) {
    return (b < 16 ? '0' : '') + b.toString(16);
  }).join(' '), ')');
  var parentIndex = startIndex;
  var parentValue = ml_dec16(ml, offset + parentIndex * 2);
  var leftIndex = ml_heapLeft(parentIndex);
  TRACE('     -- first leftIndex=', leftIndex, 'end=', endIndex);

  while (leftIndex <= endIndex) {
    TRACE('       - sift loop. indexes; parent=', parentIndex, 'left=', leftIndex, 'right=', ml_heapRight(parentIndex), 'values; parent=', _dec16(ml, offset + parentIndex * 2) + '/' + parentValue, ' left=', _dec16(ml, offset + leftIndex * 2), ' right=', ml_heapRight(parentIndex) <= endIndex ? _dec16(ml, offset + ml_heapRight(parentIndex) * 2) : 'void');
    var leftValue = ml_dec16(ml, offset + leftIndex * 2);
    var swapIndex = parentIndex;
    var swapValue = parentValue;
    TRACE('         - swap<left?', swapValue, leftValue, swapValue < leftValue ? 'yes' : 'no');

    if (swapValue < leftValue) {
      swapIndex = leftIndex;
      swapValue = leftValue;
    }

    var rightIndex = ml_heapRight(parentIndex);
    TRACE('         - right index', rightIndex, '<=', endIndex, rightIndex <= endIndex ? 'yes it has a right child' : 'no right child');

    if (rightIndex <= endIndex) {
      var rightValue = ml_dec16(ml, offset + rightIndex * 2);
      TRACE('         - swap<right?', swapValue, rightValue);

      if (swapValue < rightValue) {
        swapIndex = rightIndex;
        swapValue = rightValue;
      }
    }

    TRACE('           - result; parent=', parentIndex, 'swap=', swapIndex, ', values; parent=', parentValue, ', swap=', swapValue, '->', swapIndex === parentIndex ? 'finished, parent=swap' : 'should swap');

    if (swapIndex === parentIndex) {
      TRACE('     - ml_heapRepair end early:', 'Uint8Array(', [].map.call(ml.slice(offset + startIndex * 2, offset + startIndex * 2 + (endIndex - startIndex + 1) * 2), function (b) {
        return (b < 16 ? '0' : '') + b.toString(16);
      }).join(' '), ')');
      return;
    } // "swap"


    ml_enc16(ml, offset + parentIndex * 2, swapValue);
    ml_enc16(ml, offset + swapIndex * 2, parentValue);
    TRACE('             - setting parent to index=', swapIndex, ', value=', swapValue);
    parentIndex = swapIndex; // Note: parentValue remains the same because the swapped child becomes the new parent and it gets the old parent value

    leftIndex = ml_heapLeft(parentIndex);
    TRACE('           - next left:', leftIndex, 'end:', endIndex);
  }

  TRACE('     - ml_heapRepair end:', ml.slice(offset + startIndex * 2, offset + startIndex * 2 + (endIndex - startIndex + 1) * 2).join(' '));
}

function ml_swap16(ml, indexA, indexB) {
  var A = ml_dec16(ml, indexA);
  var B = ml_dec16(ml, indexB);
  ml_enc16(ml, indexA, B);
  ml_enc16(ml, indexB, A);
}

var bounty_flagCounter = 0;
var BOUNTY_FLAG_NOT_BOOLY = ++bounty_flagCounter; // Booly = when only used in bool ops (like nall) or as the lhs of a reifier

var BOUNTY_FLAG_OTHER = ++bounty_flagCounter;
var BOUNTY_FLAG_DIFF = 1 << ++bounty_flagCounter;
var BOUNTY_FLAG_IMP_LHS = 1 << ++bounty_flagCounter;
var BOUNTY_FLAG_IMP_RHS = 1 << ++bounty_flagCounter;
var BOUNTY_FLAG_ISALL_ARG = 1 << ++bounty_flagCounter;
var BOUNTY_FLAG_ISALL_RESULT = 1 << ++bounty_flagCounter;
var BOUNTY_FLAG_ISLTE_ARG = 1 << ++bounty_flagCounter;
var BOUNTY_FLAG_ISSAME_ARG = 1 << ++bounty_flagCounter;
var BOUNTY_FLAG_ISSAME_RESULT = 1 << ++bounty_flagCounter;
var BOUNTY_FLAG_ISSOME_RESULT = 1 << ++bounty_flagCounter;
var BOUNTY_FLAG_LTE_LHS = 1 << ++bounty_flagCounter;
var BOUNTY_FLAG_LTE_RHS = 1 << ++bounty_flagCounter;
var BOUNTY_FLAG_NALL = 1 << ++bounty_flagCounter;
var BOUNTY_FLAG_SOME = 1 << ++bounty_flagCounter;
var BOUNTY_FLAG_SUM_RESULT = 1 << ++bounty_flagCounter;
var BOUNTY_FLAG_XOR = 1 << ++bounty_flagCounter;
var BOUNTY_JUST_IGNORE = 1 << ++bounty_flagCounter;
ASSERT(bounty_flagCounter <= 32, 'can only run with 16 flags, or must increase flag size');
var BOUNTY_LINK_COUNT = 1; // Should it simply trunc over 255?

var BOUNTY_META_FLAGS = 32; // Steps of 8 (bits per byte)

var BOUNTY_MAX_OFFSETS_TO_TRACK = 20; // Perf case bounty size when this is: 5->1mb, 20->3mb

var BOUNTY_BYTES_PER_OFFSET = 4;
var BOUNTY_SIZEOF_HEADER = BOUNTY_LINK_COUNT + BOUNTY_META_FLAGS / 2;
var BOUNTY_SIZEOF_OFFSETS = BOUNTY_MAX_OFFSETS_TO_TRACK * BOUNTY_BYTES_PER_OFFSET; // Need to store 32bit per offset (more like 24 but whatever)

var BOUNTY_SIZEOF_VAR = BOUNTY_SIZEOF_HEADER + BOUNTY_SIZEOF_OFFSETS;
/**
 * @param {Uint8Array} ml
 * @param {Object} problem
 * @param {Uint8Array} [bounty]
 */

function bounty_collect(ml, problem, bounty) {
  TRACE('\n ## bounty_collect', ml.length < 50 ? ml.join(' ') : '');
  var varNames = problem.varNames,
      getAlias = problem.getAlias,
      getDomain = problem.getDomain;
  var varCount = varNames.length;
  var pc = 0;

  if (!bounty) {
    bounty = new Uint8Array(varCount * BOUNTY_SIZEOF_VAR);
    TRACE('Created bounty buffer. Size:', bounty.length);
  }

  bounty.fill(0); // Even for new buffer because they are not guaranteed to be zero filled (most like not)

  ASSERT(bounty instanceof Uint8Array);
  bountyLoop(); // Note: do not auto-mark booly-pairs as BOOLY here! (for example `x^y,x!=z` could break if x!=y)

  TRACE(" - There are " + getDeadCount(bounty) + " dead vars, " + getLeafCount(bounty) + " leaf vars, full distribution: " + getOccurrenceCount(bounty) + " other vars");
  return bounty;

  function getBountyOffset(varIndex) {
    return varIndex * BOUNTY_SIZEOF_VAR;
  }

  function getOffsetsOffset(varIndex) {
    return varIndex * BOUNTY_SIZEOF_VAR + BOUNTY_SIZEOF_HEADER;
  }

  function collect(delta, metaFlags) {
    TRACE('   ! collect(', delta, ',', _bounty__debugMeta(metaFlags), ')');
    ASSERT(typeof delta === 'number' && delta > 0, 'delta should be >0 number', delta);
    ASSERT(pc + delta > 0 && pc + delta < ml.length, 'offset should be within bounds of ML');
    ASSERT(typeof metaFlags === 'number' && metaFlags > 0, 'at least one metaFlags should be passed on', metaFlags, metaFlags.toString(2));
    var index = ml_dec16(ml, pc + delta);
    ASSERT(typeof index === 'number', 'fetched index should be number');
    ASSERT(!isNaN(index) && index >= 0 && index <= 0xffff, 'should be a valid index', index);
    index = getAlias(index);
    ASSERT(typeof index === 'number', 'fetched alias should be number');
    ASSERT(!isNaN(index) && index >= 0 && index <= 0xffff, 'should be a valid index', index);
    var domain = getDomain(index, true);
    TRACE('     - index=', index, 'domain=', domain__debug(domain));
    ASSERT_NORDOM(domain);

    if (domain_getValue(domain) >= 0) {
      TRACE('      - ignore all constants. solved vars and constants are not relevant to bounty');
      return;
    }

    var varOffset = getBountyOffset(index); // ASSERT(bounty[varOffset] < 0xff, 'constraint count should not overflow');

    var countIndex = bounty[varOffset]++; // Count, but as zero-offset

    var flagsOffset = varOffset + BOUNTY_LINK_COUNT;

    if (countIndex >= 0xff) {
      // Hardcoded limit. just ignore this var. we cant safely optimize this.
      ASSERT(BOUNTY_META_FLAGS === 32, 'update code if this changes');

      _enc32(bounty, flagsOffset, BOUNTY_JUST_IGNORE);
    } else {
      ASSERT(BOUNTY_META_FLAGS === 32, 'update code if this changes because they currently only write 16bits');

      var currentFlags = _dec32$1(bounty, flagsOffset);

      TRACE('     >> collecting for index=', index, ' -> count now:', bounty[varOffset], 'flags:', _bounty__debugMeta(currentFlags), '|=', _bounty__debugMeta(metaFlags), ' -> ', _bounty__debugMeta(currentFlags | metaFlags), 'from', flagsOffset, 'domain:', domain__debug(domain));

      if (countIndex < BOUNTY_MAX_OFFSETS_TO_TRACK) {
        var offsetsOffset = getOffsetsOffset(index);
        var nextOffset = offsetsOffset + countIndex * BOUNTY_BYTES_PER_OFFSET;
        TRACE('       - tracking offset; countIndex=', countIndex, ', putting offset at', nextOffset);

        _enc32(bounty, nextOffset, pc);
      } else {
        TRACE('       - unable to track offset; countIndex beyond max;', countIndex, '>', BOUNTY_MAX_OFFSETS_TO_TRACK);
      }

      ASSERT(BOUNTY_META_FLAGS === 32, 'update code if this changes');

      _enc32(bounty, flagsOffset, currentFlags | metaFlags);
    }
  }

  function bountyLoop() {
    pc = 0;
    TRACE(' - bountyLoop');

    while (pc < ml.length) {
      var pcStart = pc;
      var op = ml[pc];
      TRACE(' -- CT pc=' + pc + ', op: ' + ml__debug(ml, pc, 1, problem));

      switch (op) {
        case ML_LT:
          // Lt always has 2 args (any other wouldnt make sense) but is still a c-args op
          collect(OFFSET_C_A, BOUNTY_FLAG_OTHER | BOUNTY_FLAG_NOT_BOOLY);
          collect(OFFSET_C_B, BOUNTY_FLAG_OTHER | BOUNTY_FLAG_NOT_BOOLY);
          pc += SIZEOF_C_2;
          break;

        case ML_LTE:
          // Lte always has 2 args (any other wouldnt make sense) but is still a c-args op
          collect(OFFSET_C_A, BOUNTY_FLAG_LTE_LHS | BOUNTY_FLAG_NOT_BOOLY);
          collect(OFFSET_C_B, BOUNTY_FLAG_LTE_RHS | BOUNTY_FLAG_NOT_BOOLY);
          pc += SIZEOF_C_2;
          break;

        case ML_XOR:
          {
            // Xor always has 2 args (any other wouldnt make sense) but is still a c-args op
            collect(OFFSET_C_A, BOUNTY_FLAG_XOR);
            collect(OFFSET_C_B, BOUNTY_FLAG_XOR);
            pc += SIZEOF_C_2;
            break;
          }

        case ML_XNOR:
          {
            var nlen = ml_dec16(ml, pc + 1);

            for (var i = 0; i < nlen; ++i) {
              collect(SIZEOF_C + i * 2, BOUNTY_FLAG_OTHER);
            }

            pc += SIZEOF_C + nlen * 2;
            break;
          }

        case ML_IMP:
          collect(OFFSET_C_A, BOUNTY_FLAG_IMP_LHS);
          collect(OFFSET_C_B, BOUNTY_FLAG_IMP_RHS);
          pc += SIZEOF_C_2;
          break;

        case ML_NIMP:
          collect(OFFSET_C_A, BOUNTY_FLAG_OTHER);
          collect(OFFSET_C_B, BOUNTY_FLAG_OTHER);
          pc += SIZEOF_C_2;
          break;

        case ML_ALL:
          {
            var _nlen = ml_dec16(ml, pc + 1);

            for (var _i = 0; _i < _nlen; ++_i) {
              collect(SIZEOF_C + _i * 2, BOUNTY_FLAG_OTHER);
            }

            pc += SIZEOF_C + _nlen * 2;
            break;
          }

        case ML_NALL:
          {
            var _nlen2 = ml_dec16(ml, pc + 1);

            for (var _i2 = 0; _i2 < _nlen2; ++_i2) {
              collect(SIZEOF_C + _i2 * 2, BOUNTY_FLAG_NALL);
            }

            pc += SIZEOF_C + _nlen2 * 2;
            break;
          }

        case ML_SAME:
          {
            // Should be aliased but if the problem rejected there may be eqs like this left
            // (bounty is also used for generating the dsl problem)
            var _nlen3 = ml_dec16(ml, pc + 1);

            for (var _i3 = 0; _i3 < _nlen3; ++_i3) {
              collect(SIZEOF_C + _i3 * 2, BOUNTY_FLAG_OTHER | BOUNTY_FLAG_NOT_BOOLY);
            }

            pc += SIZEOF_C + _nlen3 * 2;
            break;
          }

        case ML_SOME:
          {
            var _nlen4 = ml_dec16(ml, pc + 1);

            for (var _i4 = 0; _i4 < _nlen4; ++_i4) {
              collect(SIZEOF_C + _i4 * 2, BOUNTY_FLAG_SOME);
            }

            pc += SIZEOF_C + _nlen4 * 2;
            break;
          }

        case ML_NONE:
          {
            var _nlen5 = ml_dec16(ml, pc + 1);

            for (var _i5 = 0; _i5 < _nlen5; ++_i5) {
              collect(SIZEOF_C + _i5 * 2, BOUNTY_FLAG_OTHER);
            }

            pc += SIZEOF_C + _nlen5 * 2;
            break;
          }

        case ML_ISSAME:
          {
            var _nlen6 = ml_dec16(ml, pc + 1);

            for (var _i6 = 0; _i6 < _nlen6; ++_i6) {
              collect(SIZEOF_C + _i6 * 2, BOUNTY_FLAG_ISSAME_ARG | BOUNTY_FLAG_NOT_BOOLY);
            }

            collect(SIZEOF_C + _nlen6 * 2, BOUNTY_FLAG_ISSAME_RESULT); // R

            pc += SIZEOF_C + _nlen6 * 2 + 2;
            break;
          }

        case ML_ISSOME:
          {
            var ilen = ml_dec16(ml, pc + 1);

            for (var _i7 = 0; _i7 < ilen; ++_i7) {
              collect(SIZEOF_C + _i7 * 2, BOUNTY_FLAG_OTHER);
            }

            collect(SIZEOF_C + ilen * 2, BOUNTY_FLAG_ISSOME_RESULT); // R

            pc += SIZEOF_C + ilen * 2 + 2;
            break;
          }

        case ML_DIFF:
          {
            // Note: diff "cant" have multiple counts of same var because that would reject
            var dlen = ml_dec16(ml, pc + 1);

            for (var _i8 = 0; _i8 < dlen; ++_i8) {
              collect(SIZEOF_C + _i8 * 2, BOUNTY_FLAG_DIFF | BOUNTY_FLAG_NOT_BOOLY);
            }

            pc += SIZEOF_C + dlen * 2;
            break;
          }

        case ML_ISDIFF:
          {
            var _ilen = ml_dec16(ml, pc + 1);

            for (var _i9 = 0; _i9 < _ilen; ++_i9) {
              collect(SIZEOF_C + _i9 * 2, BOUNTY_FLAG_OTHER | BOUNTY_FLAG_NOT_BOOLY);
            }

            collect(SIZEOF_C + _ilen * 2, BOUNTY_FLAG_OTHER); // R

            pc += SIZEOF_C + _ilen * 2 + 2;
            break;
          }

        case ML_ISLT:
          collect(1, BOUNTY_FLAG_OTHER | BOUNTY_FLAG_NOT_BOOLY);
          collect(3, BOUNTY_FLAG_OTHER | BOUNTY_FLAG_NOT_BOOLY);
          collect(5, BOUNTY_FLAG_OTHER);
          pc += SIZEOF_VVV;
          break;

        case ML_ISLTE:
          collect(1, BOUNTY_FLAG_ISLTE_ARG | BOUNTY_FLAG_NOT_BOOLY);
          collect(3, BOUNTY_FLAG_ISLTE_ARG | BOUNTY_FLAG_NOT_BOOLY);
          collect(5, BOUNTY_FLAG_OTHER);
          pc += SIZEOF_VVV;
          break;

        case ML_MINUS:
        case ML_DIV:
          collect(1, BOUNTY_FLAG_OTHER | BOUNTY_FLAG_NOT_BOOLY);
          collect(3, BOUNTY_FLAG_OTHER | BOUNTY_FLAG_NOT_BOOLY);
          collect(5, BOUNTY_FLAG_OTHER | BOUNTY_FLAG_NOT_BOOLY);
          pc += SIZEOF_VVV;
          break;

        case ML_ISALL:
          {
            var _ilen2 = ml_dec16(ml, pc + 1);

            for (var _i10 = 0; _i10 < _ilen2; ++_i10) {
              collect(SIZEOF_C + _i10 * 2, BOUNTY_FLAG_ISALL_ARG);
            }

            collect(SIZEOF_C + _ilen2 * 2, BOUNTY_FLAG_ISALL_RESULT); // R

            pc += SIZEOF_C + _ilen2 * 2 + 2;
            break;
          }

        case ML_ISNALL:
        case ML_ISNONE:
          {
            var mlen = ml_dec16(ml, pc + 1);

            for (var _i11 = 0; _i11 < mlen; ++_i11) {
              collect(SIZEOF_C + _i11 * 2, BOUNTY_FLAG_OTHER);
            }

            collect(SIZEOF_C + mlen * 2, BOUNTY_FLAG_OTHER);
            pc += SIZEOF_C + mlen * 2 + 2;
            break;
          }

        case ML_SUM:
          {
            // TODO: collect multiple occurrences of same var once
            var splen = ml_dec16(ml, pc + 1);

            for (var _i12 = 0; _i12 < splen; ++_i12) {
              collect(SIZEOF_C + _i12 * 2, BOUNTY_FLAG_OTHER | BOUNTY_FLAG_NOT_BOOLY);
            }

            collect(SIZEOF_C + splen * 2, BOUNTY_FLAG_SUM_RESULT | BOUNTY_FLAG_NOT_BOOLY); // R

            pc += SIZEOF_C + splen * 2 + 2;
            break;
          }

        case ML_PRODUCT:
          {
            // TODO: collect multiple occurrences of same var once
            var plen = ml_dec16(ml, pc + 1);

            for (var _i13 = 0; _i13 < plen; ++_i13) {
              collect(SIZEOF_C + _i13 * 2, BOUNTY_FLAG_OTHER | BOUNTY_FLAG_NOT_BOOLY);
            }

            collect(SIZEOF_C + plen * 2, BOUNTY_FLAG_OTHER | BOUNTY_FLAG_NOT_BOOLY); // R

            pc += SIZEOF_C + plen * 2 + 2;
            break;
          }

        case ML_START:
          if (pc !== 0) return THROW(' ! compiler problem @', pcStart);
          ++pc;
          break;

        case ML_STOP:
          return;

        case ML_NOBOOL:
          // For testing, consider vars under nobool explicitly not-booly
          collect(1, BOUNTY_FLAG_OTHER | BOUNTY_FLAG_NOT_BOOLY);
          pc += SIZEOF_V;
          break;

        case ML_NOLEAF:
          // Should prevent trivial eliminations because ML_NOLEAF is never part of a trick
          // vars under ML_NOLEAF are explicitly never considered leaf vars because their counts is inflated
          collect(1, BOUNTY_FLAG_OTHER);
          pc += SIZEOF_V;
          break;

        case ML_JMP:
          pc += SIZEOF_V + ml_dec16(ml, pc + 1);
          break;

        case ML_JMP32:
          pc += SIZEOF_W + ml_dec32(ml, pc + 1);
          break;

        case ML_NOOP:
          ++pc;
          break;

        case ML_NOOP2:
          pc += 2;
          break;

        case ML_NOOP3:
          pc += 3;
          break;

        case ML_NOOP4:
          pc += 4;
          break;

        default:
          // Put in a switch in the default so that the main switch is smaller. this second switch should never hit.
          getTerm().error('(cnt) unknown op', pc, ' at', pc);
          ml_throw(ml, pc, '(bnt) expecting bounty to run after the minifier and these ops should be gone');
      }
    }

    ml_throw(ml, pc, 'ML OOB');
  }

  function getDeadCount(varMeta) {
    var count = 0;

    for (var i = 0; i < varCount; i += BOUNTY_SIZEOF_VAR) {
      if (!varMeta[i]) ++count;
    }

    return count;
  }

  function getLeafCount(varMeta) {
    var count = 0;

    for (var i = 0; i < varCount; i += BOUNTY_SIZEOF_VAR) {
      if (varMeta[i] === 1) ++count;
    }

    return count;
  }

  function getOccurrenceCount(varMeta) {
    // Should be eliminated when not used by ASSERTs
    var count = {};

    for (var i = 0; i < varCount; i += BOUNTY_SIZEOF_VAR) {
      count[varMeta[i]] = ~-count[varMeta[i]];
    }

    return count;
  }
}

function bounty_getCounts(bounty, varIndex) {
  return bounty[varIndex * BOUNTY_SIZEOF_VAR];
}

function bounty_markVar(bounty, varIndex) {
  ASSERT(typeof bounty === 'object', 'bounty should be object');
  ASSERT(typeof varIndex === 'number' && varIndex >= 0, 'should be valid varIndex'); // Until next loop, ignore this var (need to refresh bounty data)

  TRACE(' - bounty_markVar', varIndex);
  bounty[varIndex * BOUNTY_SIZEOF_VAR] = 0;
}

function bounty_getMeta(bounty, varIndex, _debug) {
  ASSERT(bounty_getCounts(bounty, varIndex) > 0 || _debug, 'check caller (2), this is probably a bug (var did not appear in any constraint, or its a constant, or this data was marked as stale)');
  return _dec32$1(bounty, varIndex * BOUNTY_SIZEOF_VAR + BOUNTY_LINK_COUNT);
}

function bounty_getOffset(bounty, varIndex, n, _debug) {
  ASSERT(bounty_getCounts(bounty, varIndex) > 0 || _debug, 'check caller (1), this is probably a bug (var did not appear in any constraint, or its a constant, or this data was marked as stale)', varIndex, n, bounty_getCounts(bounty, varIndex), _debug);
  ASSERT(n < bounty_getCounts(bounty, varIndex), 'check caller, this is probably a bug (should not get an offset beyond the count)');
  ASSERT(n < BOUNTY_MAX_OFFSETS_TO_TRACK, 'OOB, shouldnt exceed the max offset count', n, '<', BOUNTY_MAX_OFFSETS_TO_TRACK);
  return _dec32$1(bounty, varIndex * BOUNTY_SIZEOF_VAR + BOUNTY_SIZEOF_HEADER + n * BOUNTY_BYTES_PER_OFFSET);
}

function bounty__debug(bounty, varIndex, full) {
  var count = bounty_getCounts(bounty, varIndex);
  var r = "{B: index=" + varIndex + ", counts=" + count + ", meta=" + bounty__debugMeta(bounty, varIndex);

  if (full) {
    r += ', offsets:[';

    for (var i = 0; i < BOUNTY_MAX_OFFSETS_TO_TRACK; ++i) {
      if (i) r += ', ';
      if (i >= count) r += '(';
      r += _dec32$1(bounty, varIndex * BOUNTY_SIZEOF_VAR + BOUNTY_SIZEOF_HEADER + i * BOUNTY_BYTES_PER_OFFSET);
      if (i >= count) r += ')';
    }

    r += ']';
  }

  return r + '}';
}

function bounty__debugMeta(bounty, index) {
  ASSERT(typeof bounty === 'object', 'bounty object');
  ASSERT(typeof index === 'number', 'the index should be a number', index);
  var counts = bounty_getCounts(bounty, index) | 0; // Constants would return undefined here

  if (counts === 0) return '[ constant or marked var ]';
  var meta = counts && bounty_getMeta(bounty, index, true);
  return _bounty__debugMeta(meta);
}

function _bounty__debugMeta(meta) {
  ASSERT(typeof meta === 'number', 'the meta should be a number', meta);
  var s = '0'.repeat(32 - meta.toString(2).length) + meta.toString(2);
  var what = [];
  if (!meta) what.push('BOUNTY_NONE');

  if ((meta & BOUNTY_FLAG_NOT_BOOLY) === BOUNTY_FLAG_NOT_BOOLY) {
    what.push('NOT_BOOLY');
  } else {
    what.push('BOOLY');
  }

  if ((meta & BOUNTY_FLAG_OTHER) === BOUNTY_FLAG_OTHER) what.push('OTHER');
  if ((meta & BOUNTY_FLAG_LTE_LHS) === BOUNTY_FLAG_LTE_LHS) what.push('LTE_LHS');
  if ((meta & BOUNTY_FLAG_LTE_RHS) === BOUNTY_FLAG_LTE_RHS) what.push('LTE_RHS');
  if ((meta & BOUNTY_FLAG_ISALL_ARG) === BOUNTY_FLAG_ISALL_ARG) what.push('ISALL_ARG');
  if ((meta & BOUNTY_FLAG_ISALL_RESULT) === BOUNTY_FLAG_ISALL_RESULT) what.push('ISALL_RESULT');
  if ((meta & BOUNTY_FLAG_IMP_LHS) === BOUNTY_FLAG_IMP_LHS) what.push('IMP_LHS');
  if ((meta & BOUNTY_FLAG_IMP_RHS) === BOUNTY_FLAG_IMP_RHS) what.push('IMP_RHS');
  if ((meta & BOUNTY_FLAG_ISLTE_ARG) === BOUNTY_FLAG_ISLTE_ARG) what.push('ISLTE_ARG');
  if ((meta & BOUNTY_FLAG_ISSAME_ARG) === BOUNTY_FLAG_ISSAME_ARG) what.push('ISSAME_ARG');
  if ((meta & BOUNTY_FLAG_ISSAME_RESULT) === BOUNTY_FLAG_ISSAME_RESULT) what.push('ISSAME_RESULT');
  if ((meta & BOUNTY_FLAG_ISSOME_RESULT) === BOUNTY_FLAG_ISSOME_RESULT) what.push('ISSOME_RESULT');
  if ((meta & BOUNTY_FLAG_NALL) === BOUNTY_FLAG_NALL) what.push('NALL');
  if ((meta & BOUNTY_FLAG_DIFF) === BOUNTY_FLAG_DIFF) what.push('DIFF');
  if ((meta & BOUNTY_FLAG_SOME) === BOUNTY_FLAG_SOME) what.push('SOME');
  if ((meta & BOUNTY_FLAG_SUM_RESULT) === BOUNTY_FLAG_SUM_RESULT) what.push('SUM_RESULT');
  if ((meta & BOUNTY_FLAG_XOR) === BOUNTY_FLAG_XOR) what.push('XOR');
  if ((meta & BOUNTY_JUST_IGNORE) === BOUNTY_JUST_IGNORE) what.push('JUST_IGNORE');
  return '[ ' + s + ': ' + what.join(', ') + ' ]';
}

function _dec32$1(bounty, offset) {
  ASSERT(bounty instanceof Uint8Array, 'should be Uint8Array');
  ASSERT(typeof offset === 'number' && offset >= 0 && offset < bounty.length, 'Invalid or OOB', offset, '>=', bounty.length);
  return bounty[offset++] << 24 | bounty[offset++] << 16 | bounty[offset++] << 8 | bounty[offset];
}

function _enc32(bounty, offset, num) {
  ASSERT(bounty instanceof Uint8Array, 'should be Uint8Array');
  ASSERT(typeof offset === 'number' && offset >= 0 && offset < bounty.length, 'Invalid or OOB', offset, '>=', bounty.length);
  ASSERT(typeof num === 'number', 'Encoding numbers');
  ASSERT(num <= 0xffffffff, 'implement 64bit index support if this breaks', num);
  ASSERT(num >= 0, 'only expecting non-negative nums', num);
  bounty[offset++] = num >> 24 & 0xff;
  bounty[offset++] = num >> 16 & 0xff;
  bounty[offset++] = num >> 8 & 0xff;
  bounty[offset] = num & 0xff;
}

// TODO: need to update this code to use getDomain and aliases and such
/**
 * Generate a dsl for given ml
 * Includes a full debugging output stack to investigate a problem more thoroughly
 *
 * @param {Uint8Array} ml
 * @param {Object} problem
 * @param {number[]} [bounty]
 * @param {Object} options See preSolver options
 * @returns {string}
 */

function ml2dsl(ml, problem, bounty, options) {
  TRACE('\n## ml2dsl');
  var DEBUG = Boolean(options.debugDsl); // Add debugging help in comments (domains, related constraints, occurrences, etc)

  var HASH_NAMES = Boolean(options.hashNames); // Replace all var varNames with $index$ with index in base36

  var INDEX_NAMES = Boolean(options.indexNames); // Replace all var varNames with _index_ (ignored if HASH_NAMES is true)

  var ADD_GROUPED_CONSTRAINTS = Boolean(options.groupedConstraints); // Only used when debugging

  var varNames = problem.varNames,
      domains = problem.domains,
      valdist = problem.valdist,
      getDomain = problem.getDomain,
      getAlias = problem.getAlias,
      solveStack = problem.solveStack,
      targeted = problem.targeted;
  var pc = 0;
  var dsl = '';
  var LEN = ml.length;

  function toName(index) {
    if (HASH_NAMES) return '$' + index.toString(36) + '$';
    if (INDEX_NAMES) return '_' + index + '_';
    return varNames[index];
  }

  function valueOrName(a, vA) {
    if (vA >= 0) return vA;
    return toName(a);
  }

  function domainstr(A, vA) {
    if (vA >= 0) return 'lit(' + vA + ')';
    return domain__debug(A);
  }

  function counts(index) {
    var c = bounty_getCounts(bounty, index);
    if (c === undefined) return '-';
    return c;
  }

  var allParts = [];
  var partsPerVar = [];
  var varOps = [];
  var constraintCount = 0;
  m2d_innerLoop();

  if (DEBUG) {
    var varDecls = [];
    var varsLeft = 0;
    var aliases = 0;
    var solved = 0;
    var unsolved = 0; // First generate var decls for unsolved, unaliased vars

    domains.forEach(function (domain, index) {
      var str = '';

      if (domain === false || bounty && !counts(index)) {
        // Either solved, alias, or leaf. leafs still needs to be updated after the rest solves.
        domain = getDomain(index);

        if (domain_getValue(domain) >= 0) {
          ++solved;
        } else {
          ++aliases;
        }
      } else {
        ++varsLeft;
        ASSERT(domain === getDomain(index), 'if not aliased then it should return this', index, domain);
        ASSERT(domain_getValue(domain) < 0, 'solved vars should be aliased to their constant');
        ++unsolved;
        str = ': ' + toName(index) + ' [' + domain_toArr(domain) + ']';
        var vardist = valdist[index];

        if (vardist) {
          switch (vardist.valtype) {
            case 'max':
            case 'mid':
            case 'min':
            case 'naive':
              str += ' @' + vardist.valtype;
              break;

            case 'list':
              str += ' @' + vardist.valtype;
              str += ' prio(' + vardist.list + ')';
              break;

            case 'markov':
              str += ' # skipping markov dist (no longer supported)';
              break;

            case 'minMaxCycle':
            case 'splitMax':
            case 'splitMin':
            default:
              THROW('unknown var dist [' + vardist.valtype + '] ' + JSON.stringify(vardist));
          }
        }
      }

      varDecls[index] = str;
    });
    var varDeclsString = domains.map(function (_, varIndex) {
      // ignore constants, aliases, and leafs
      if (domains[varIndex] === false) return '';
      var cnts = counts(varIndex);
      if (!cnts) return '';
      var decl = varDecls[varIndex];
      ASSERT(varOps[varIndex], 'anything that has counts should have varOps of those constraints', 'var index:', varIndex, 'counts:', cnts, ', varops:', varOps[varIndex], ', decls:', decl, ', name:', varNames[varIndex], ', ppv:', partsPerVar[varIndex], '->', partsPerVar[varIndex] && partsPerVar[varIndex].map(function (partIndex) {
        return allParts[partIndex];
      }));
      ASSERT(decl, 'anything that has counts should have that many constraints', 'var index:', varIndex, 'counts:', cnts, ', varops:', varOps[varIndex], ', decls:', decl, ', name:', varNames[varIndex], ', ppv:', partsPerVar[varIndex]);
      var ops = varOps[varIndex].split(/ /g).sort().join(' ');
      return decl + ' # T:' + targeted[varIndex] + ' ' + ' # ocounts: ' + cnts + (HASH_NAMES || !INDEX_NAMES ? '  # index = ' + varIndex : '') + '  # ops (' + (ops.replace(/[^ ]/g, '').length + 1) + '): ' + ops + ' $ meta: ' + bounty__debugMeta(bounty, varIndex) + (ADD_GROUPED_CONSTRAINTS && partsPerVar[varIndex] ? '\n ## ' + partsPerVar[varIndex].map(function (partIndex) {
        return allParts[partIndex];
      }).join(' ## ') : '');
    }).filter(function (s) {
      return Boolean(s);
    }).join('\n');
    dsl = "\n# Constraints: " + constraintCount + " x\n# Vars: " + domains.length + " x\n#   Aliases: " + aliases + " x\n#   Domained: " + varsLeft + " x\n#    - Solved: " + solved + " x\n#    - Unsolved: " + unsolved + " x\n#    - Solve stack: " + solveStack.length + " x (or " + (solveStack.length - aliases) + " x without aliases)\n";
    getTerm().log(dsl);
    dsl += "\n# Var decls:\n" + varDeclsString + "\n\n";
  } else {
    dsl += '# vars (' + domains.length + 'x total):\n';
    dsl += domains.map(function (d, i) {
      return [d, i];
    }).filter(function (a) {
      return a[0] !== false;
    }).filter(function (a) {
      return !bounty || counts(a[1]) > 0;
    }).map(function (a) {
      return ': ' + toName(a[1]) + ' [' + domain_toArr(a[0]) + ']';
    }).join('\n');
    dsl += '\n\n';
  }

  dsl += '\n# Constraints (' + allParts.length + 'x):\n' + allParts.join('');
  dsl += String('\n# Meta:\n' + m2d_getTargetsDirective());
  return dsl; // ###########################################

  function m2d_dec16() {
    ASSERT(pc < LEN - 1, 'OOB');
    TRACE(' . dec16 decoding', ml[pc] << 8, 'from', pc, 'and', ml[pc + 1], 'from', pc + 1, '=>', ml[pc] << 8 | ml[pc + 1]);
    var s = ml[pc++] << 8 | ml[pc++];
    return s;
  }

  function m2d_dec32() {
    ASSERT(pc < LEN - 1, 'OOB');
    TRACE(' . dec32 decoding', ml[pc], ml[pc + 1], ml[pc + 2], ml[pc + 3], 'from', pc, '=>', ml[pc] << 8 | ml[pc + 1]);
    return ml[pc++] << 24 | ml[pc++] << 16 | ml[pc++] << 8 | ml[pc++];
  }

  function m2d_decA(op, skipIfConstant) {
    ASSERT(typeof op === 'string' && op, 'op should be string');
    var a = getAlias(m2d_dec16());
    var A = getDomain(a);
    var vA = domain_getValue(A);
    if (vA >= 0 && skipIfConstant) return false;

    if (DEBUG) {
      if (vA < 0) {
        if (!partsPerVar[a]) partsPerVar[a] = [];
        partsPerVar[a].push(allParts.length);
        varOps[a] = (varOps[a] === undefined ? '' : varOps[a] + ' ') + op;
      }

      var s = valueOrName(a, vA);
      s += ' '.repeat(Math.max(45 - s.length, 3));
      s += '# ' + domainstr(A, vA);
      s += ' '.repeat(Math.max(110 - s.length, 3));
      s += '# args: ' + a;
      s += ' '.repeat(Math.max(150 - s.length, 3));
      if (bounty) s += '# counts: ' + counts(a) + ' ';
      s += ' \n';
      return s;
    }

    return valueOrName(a, vA);
  }

  function _m2d_decAb(op, a, b) {
    var A = getDomain(a);
    var vA = domain_getValue(A);
    var B = getDomain(b);
    var vB = domain_getValue(B);
    return __m2d_decAb(op, a, A, vA, b, B, vB);
  }

  function __m2d_decAb(op, a, A, vA, b, B, vB) {
    if (DEBUG) {
      if (vA < 0) {
        // Else is probably dead code; all binary void constraints with a constant get resolved immediately
        if (!partsPerVar[a]) partsPerVar[a] = [];
        partsPerVar[a].push(allParts.length);
        varOps[a] = (varOps[a] === undefined ? '' : varOps[a] + ' ') + op;
      }

      if (vB < 0) {
        // Else is probably dead code; all binary void constraints with a constant get resolved immediately
        if (!partsPerVar[b]) partsPerVar[b] = [];
        partsPerVar[b].push(allParts.length);
        varOps[b] = (varOps[b] === undefined ? '' : varOps[b] + ' ') + op;
      }

      var s = valueOrName(a, vA) + ' ' + op + ' ' + valueOrName(b, vB);
      s += ' '.repeat(Math.max(45 - s.length, 3));
      s += '# ' + domainstr(A, vA) + ' ' + op + ' ' + domainstr(B, vB);
      s += ' '.repeat(Math.max(110 - s.length, 3));
      s += '# args: ' + a + ', ' + b;
      s += ' '.repeat(Math.max(150 - s.length, 3));
      if (bounty) s += '# counts: ' + counts(a) + ' ' + op + ' ' + counts(b) + ' ';
      s += ' \n';
      return s;
    }

    return valueOrName(a, vA) + ' ' + op + ' ' + valueOrName(b, vB) + '\n';
  }

  function m2d_decAbc(op) {
    ASSERT(typeof op === 'string' && op, 'op should be string');
    var a = getAlias(m2d_dec16());
    var b = getAlias(m2d_dec16());
    var c = getAlias(m2d_dec16());
    return _m2d_decAbc(op, a, b, c);
  }

  function _m2d_decAbc(op, a, b, c) {
    var A = getDomain(a);
    var vA = domain_getValue(A);
    var B = getDomain(b);
    var vB = domain_getValue(B);
    var C = getDomain(c);
    var vC = domain_getValue(C);
    return __m2d_decAbc(op, a, A, vA, b, B, vB, c, C, vC);
  }

  function __m2d_decAbc(op, a, A, vA, b, B, vB, c, C, vC) {
    if (DEBUG) {
      if (vA < 0) {
        // Else is probably dead; args are ordered and A can only be solved if B is also solved or unordered.
        if (!partsPerVar[a]) partsPerVar[a] = [];
        partsPerVar[a].push(allParts.length);
        varOps[a] = (varOps[a] === undefined ? '' : varOps[a] + ' ') + op;
      }

      if (vB < 0) {
        if (!partsPerVar[b]) partsPerVar[b] = [];
        partsPerVar[b].push(allParts.length);
        varOps[b] = (varOps[b] === undefined ? '' : varOps[b] + ' ') + op;
      }

      if (vC < 0) {
        if (!partsPerVar[c]) partsPerVar[c] = [];
        partsPerVar[c].push(allParts.length);
        varOps[c] = (varOps[c] === undefined ? '' : varOps[c] + ' ') + op;
      }

      var s = valueOrName(c, vC) + ' = ' + valueOrName(a, vA) + ' ' + op + ' ' + valueOrName(b, vB);
      s += ' '.repeat(Math.max(45 - s.length, 3));
      s += '# ' + domainstr(C, vC) + ' = ' + domainstr(A, vA) + ' ' + op + ' ' + domainstr(B, vB);
      s += ' '.repeat(Math.max(110 - s.length, 3));
      s += '# indexes: ' + c + ' = ' + a + ' ' + op + ' ' + b;
      s += ' '.repeat(Math.max(150 - s.length, 3));
      if (bounty) s += '# counts: ' + counts(c) + ' = ' + counts(a) + ' ' + op + ' ' + counts(b) + ' ';
      s += '\n';
      return s;
    }

    return valueOrName(c, vC) + ' = ' + valueOrName(a, vA) + ' ' + op + ' ' + valueOrName(b, vB) + '\n';
  }

  function m2d_listVoid(callName) {
    ASSERT(typeof callName === 'string' && callName, 'callName should be string');
    var argCount = m2d_dec16();

    if (argCount === 2) {
      if (callName === 'all') return _m2d_decAb('&', getAlias(m2d_dec16()), getAlias(m2d_dec16()));
      if (callName === 'diff') return _m2d_decAb('!=', getAlias(m2d_dec16()), getAlias(m2d_dec16()));
      if (callName === 'imp') return _m2d_decAb('->', getAlias(m2d_dec16()), getAlias(m2d_dec16()));
      if (callName === 'lt') return _m2d_decAb('<', getAlias(m2d_dec16()), getAlias(m2d_dec16()));
      if (callName === 'lte') return _m2d_decAb('<=', getAlias(m2d_dec16()), getAlias(m2d_dec16()));
      if (callName === 'nall') return _m2d_decAb('!&', getAlias(m2d_dec16()), getAlias(m2d_dec16()));
      if (callName === 'nimp') return _m2d_decAb('!->', getAlias(m2d_dec16()), getAlias(m2d_dec16())); // If (callName === 'none') return _m2d_decAb('!|', getAlias(m2d_dec16()), getAlias(m2d_dec16()));

      if (callName === 'same') return _m2d_decAb('==', getAlias(m2d_dec16()), getAlias(m2d_dec16()));
      if (callName === 'some') return _m2d_decAb('|', getAlias(m2d_dec16()), getAlias(m2d_dec16()));
      if (callName === 'xnor') return _m2d_decAb('!^', getAlias(m2d_dec16()), getAlias(m2d_dec16()));
      if (callName === 'xor') return _m2d_decAb('^', getAlias(m2d_dec16()), getAlias(m2d_dec16()));
    }

    var indexes = '';
    var counters = '';
    var argNames = '';
    var debugs = ''; // Let prevIndex = -1;

    for (var i = 0; i < argCount; ++i) {
      var d = getAlias(m2d_dec16());
      var D = getDomain(d);
      var vD = domain_getValue(D);
      argNames += valueOrName(d, vD) + ' ';

      if (DEBUG) {
        if (vD < 0) {
          if (!partsPerVar[d]) partsPerVar[d] = [];
          partsPerVar[d].push(allParts.length);
          varOps[d] = (varOps[d] === undefined ? '' : varOps[d] + ' ') + callName;
        }

        indexes += d + ' ';
        if (bounty) counters += counts(d) + ' ';
        debugs += domainstr(D, vD) + ' ';
      }
    }

    if (DEBUG) {
      var s = callName + '( ' + argNames + ')';
      s += ' '.repeat(Math.max(45 - s.length, 3));
      s += '# ' + callName + '( ' + debugs + ') ';
      s += ' '.repeat(Math.max(110 - s.length, 3));
      s += '# indexes: ' + indexes;
      s += ' '.repeat(Math.max(150 - s.length, 3));
      if (bounty) s += '# counts: ' + callName + '( ' + counters + ')';
      s += '\n';
      return s;
    }

    return callName + '( ' + argNames + ')\n';
  }

  function m2d_listResult(callName) {
    ASSERT(typeof callName === 'string' && callName, 'callName should be string');
    var argCount = m2d_dec16();
    return m2d_listResultBody(callName, argCount);
  }

  function m2d_listResultBody(callName, argCount) {
    ASSERT(typeof callName === 'string' && callName, 'callName should be string');

    if (argCount === 2) {
      // If (callName === 'all?') return _m2d_decAbc('&?', getAlias(m2d_dec16()), getAlias(m2d_dec16()), getAlias(m2d_dec16()));
      if (callName === 'diff?') return _m2d_decAbc('!=?', getAlias(m2d_dec16()), getAlias(m2d_dec16()), getAlias(m2d_dec16())); // If (callName === 'nall?') return _m2d_decAbc('!&?', getAlias(m2d_dec16()), getAlias(m2d_dec16()), getAlias(m2d_dec16()));
      // if (callName === 'none?') return _m2d_decAbc('!|?', getAlias(m2d_dec16()), getAlias(m2d_dec16()), getAlias(m2d_dec16()));

      if (callName === 'same?') return _m2d_decAbc('==?', getAlias(m2d_dec16()), getAlias(m2d_dec16()), getAlias(m2d_dec16())); // If (callName === 'some?') return _m2d_decAbc('|?', getAlias(m2d_dec16()), getAlias(m2d_dec16()), getAlias(m2d_dec16()));

      if (callName === 'sum') return _m2d_decAbc('+', getAlias(m2d_dec16()), getAlias(m2d_dec16()), getAlias(m2d_dec16()));
      if (callName === 'product') return _m2d_decAbc('*', getAlias(m2d_dec16()), getAlias(m2d_dec16()), getAlias(m2d_dec16()));
    }

    var indexes = '';
    var counters = '';
    var argNames = '';
    var debugs = ''; // Let prevIndex = -1;

    for (var i = 0; i < argCount; ++i) {
      var d = getAlias(m2d_dec16());
      var D = getDomain(d);
      var vD = domain_getValue(D);
      argNames += valueOrName(d, vD) + ' ';

      if (DEBUG) {
        if (vD < 0) {
          if (!partsPerVar[d]) partsPerVar[d] = [];
          partsPerVar[d].push(allParts.length);
          varOps[d] = (varOps[d] === undefined ? '' : varOps[d] + ' ') + callName;
        }

        indexes += d + ' ';
        if (bounty) counters += counts(d) + ' ';
        debugs += domainstr(D, vD) + ' ';
      }
    }

    var r = getAlias(m2d_dec16());
    var R = getDomain(r);
    var vR = domain_getValue(R);

    if (DEBUG) {
      if (vR < 0) {
        if (!partsPerVar[r]) partsPerVar[r] = [];
        partsPerVar[r].push(allParts.length);
        varOps[r] = (varOps[r] === undefined ? '' : varOps[r] + ' ') + callName;
      }

      var s = valueOrName(r, vR) + ' = ' + callName + '( ' + argNames + ')';
      s += ' '.repeat(Math.max(45 - s.length, 3));
      s += '# ' + domainstr(R, vR) + ' = ' + callName + '( ' + debugs + ') ';
      s += ' '.repeat(Math.max(110 - s.length, 3));
      s += '# indexes: ' + r + ' = ' + indexes;
      s += ' '.repeat(Math.max(150 - s.length, 3));
      if (bounty) s += '# counts: ' + counts(r) + ' = ' + callName + '( ' + counters + ')';
      s += '\n';
      return s;
    }

    return valueOrName(r, vR) + ' = ' + callName + '( ' + argNames + ')\n';
  }

  function m2d_innerLoop() {
    while (pc < LEN) {
      var pcStart = pc;
      var op = ml[pc++];
      var part = '';

      switch (op) {
        case ML_START:
        case ML_STOP:
        case ML_NOBOOL:
        case ML_NOLEAF:
        case ML_NOOP:
        case ML_NOOP2:
        case ML_NOOP3:
        case ML_NOOP4:
        case ML_JMP:
        case ML_JMP32:
          break;

        default:
          ++constraintCount;
      }

      switch (op) {
        case ML_START:
          if (pc !== 1) {
            // Pc is already incremented...
            return THROW(' ! ml2dsl compiler problem @', pcStart);
          }

          break;

        case ML_STOP:
          TRACE(' ! good end @', pcStart);
          return;

        case ML_JMP:
          var delta = m2d_dec16();
          TRACE(' ! jmp', delta);
          if (delta <= 0) THROW('Must jump some bytes');
          pc += delta;
          break;

        case ML_JMP32:
          var delta32 = m2d_dec32();
          TRACE(' ! jmp32', delta32);
          if (delta32 <= 0) THROW('Must jump some bytes');
          pc += delta32;
          break;

        case ML_LT:
          TRACE(' ! lt');
          part = m2d_listVoid('lt');
          break;

        case ML_LTE:
          TRACE(' ! lte');
          part = m2d_listVoid('lte');
          break;

        case ML_XOR:
          TRACE(' ! xor');
          part = m2d_listVoid('xor');
          break;

        case ML_IMP:
          TRACE(' ! imp vv');
          part = m2d_listVoid('imp');
          break;

        case ML_NIMP:
          TRACE(' ! nimp vv');
          part = m2d_listVoid('nimp');
          break;

        case ML_ALL:
          TRACE(' ! all');
          part = m2d_listVoid('all');
          break;

        case ML_DIFF:
          TRACE(' ! diff');
          part = m2d_listVoid('diff');
          break;

        case ML_NALL:
          TRACE(' ! nall');
          part = m2d_listVoid('nall');
          break;

        case ML_NONE:
          TRACE(' ! none');
          part = m2d_listVoid('none');
          break;

        case ML_SAME:
          TRACE(' ! same');
          part = m2d_listVoid('same');
          break;

        case ML_SOME:
          TRACE(' ! some');
          part = m2d_listVoid('some');
          break;

        case ML_XNOR:
          TRACE(' ! xnor');
          part = m2d_listVoid('xnor');
          break;

        case ML_ISLT:
          TRACE(' ! islt vvv');
          part = m2d_decAbc('<?');
          break;

        case ML_ISLTE:
          TRACE(' ! islte vvv');
          part = m2d_decAbc('<=?');
          break;

        case ML_ISALL:
          TRACE(' ! isall');
          part = m2d_listResult('all?');
          break;

        case ML_ISDIFF:
          TRACE(' ! isdiff');
          part = m2d_listResult('diff?');
          break;

        case ML_ISNALL:
          TRACE(' ! isnall');
          part = m2d_listResult('nall?');
          break;

        case ML_ISNONE:
          TRACE(' ! isnone');
          part = m2d_listResult('none?');
          break;

        case ML_ISSAME:
          TRACE(' ! issame');
          part = m2d_listResult('same?');
          break;

        case ML_ISSOME:
          TRACE(' ! issome');
          part = m2d_listResult('some?');
          break;

        case ML_MINUS:
          TRACE(' ! minus');
          part = m2d_decAbc('-');
          break;

        case ML_DIV:
          TRACE(' ! div');
          part = m2d_decAbc('/');
          break;

        case ML_SUM:
          TRACE(' ! sum');
          part = m2d_listResult('sum');
          break;

        case ML_PRODUCT:
          TRACE(' ! product');
          part = m2d_listResult('product');
          break;

        case ML_NOBOOL:
          TRACE(' ! nobool'); // Fdq will understand but ignore this. skip for constants.

          var Bpart = m2d_decA('<debug>', true);
          if (Bpart !== false) part = '@custom nobool ' + Bpart + '\n';
          break;

        case ML_NOLEAF:
          TRACE(' ! noleaf'); // Fdq will understand but ignore this. skip for constants.

          var Apart = m2d_decA('<debug>', true);

          if (Apart !== false) {
            part = '@custom noleaf ' + Apart + '\n';
          }

          break;

        case ML_NOOP:
          TRACE(' ! noop');
          pc = pcStart + 1;
          break;

        case ML_NOOP2:
          TRACE(' ! noop 2');
          pc = pcStart + 2;
          break;

        case ML_NOOP3:
          TRACE(' ! noop 3');
          pc = pcStart + 3;
          break;

        case ML_NOOP4:
          TRACE(' ! noop 4');
          pc = pcStart + 4;
          break;

        default:
          ml_throw('(m2d) unknown op', pc, ' at');
      }

      allParts.push(part);
    }
  }

  function m2d_getTargetsDirective() {
    var targets = [];
    var targeted = problem.targeted;
    var len = domains.length;
    var total = 0;
    var nontargets = 0;

    for (var i = 0; i < len; ++i) {
      if (domains[i] === false) continue;
      if (!counts(i)) continue;
      ++total;

      if (!targeted[i]) {
        ++nontargets; // We only care about this state for vars that will appear in the dsl.

        continue;
      }

      targets.push(toName(i));
    } // TODO
    // what if there are no targets left? we could set internal
    // vars to anything but that could still affect targeted
    // vars through the solve stack... or perhaps they are irrelevant?
    // does this mean any valuation will work to resolve the vars?


    return '@custom targets' + (nontargets && nontargets.length ? '( ' + targets.join(' ') + ' )' : ' all') + ' # ' + (total - nontargets) + ' / ' + total + '\n';
  }
}

function m2d__debug(problem, notTrace) {
  TRACE('\nm2d__debug, temporarily disabling TRACE while generating dsl');
  var was = isTracing();
  if (!was && !notTrace) return ''; // TRACE is disabled; dont generate anything as it wont be seen (reduce test runtime)

  if (process.env.NODE_ENV !== 'production') setTracing(false);
  var dsl = ml2dsl(problem.ml, problem, bounty_collect(problem.ml, problem), {
    debugDsl: false,
    hashNames: false
  });
  if (process.env.NODE_ENV !== 'production') setTracing(was);
  return '\n## current remaining problem as dsl:\n' + dsl + '## end of current remaining problem\n';
}

// Note: you can use the tool at https://pvdz.github.io/logic-table-filter/ to test some of these tricks
var ML_BOOLY_NO = 0;
var ML_BOOLY_YES = 1;
var ML_BOOLY_MAYBE = 2;

function cutter(ml, problem, once) {
  TRACE('\n ## cutter', ml.length < 50 ? ml.join(' ') : '');
  var term = getTerm();
  var getDomain = problem.getDomain,
      setDomain = problem.setDomain,
      addAlias = problem.addAlias,
      getAlias = problem.getAlias,
      solveStack = problem.solveStack,
      leafs = problem.leafs,
      isConstant = problem.isConstant;
  var pc = 0;
  var bounty;
  var stacksBefore;
  var emptyDomain = false;
  var changes = 0;
  var loops = 0;
  var requestAnotherCycle = false; // When true this will force another cycle so the minimizer runs again

  do {
    term.time('-> cut_loop ' + loops);
    TRACE(' # start cutter outer loop', loops);
    bounty = bounty_collect(ml, problem, bounty);
    TRACE('\n#### Problem state between bounty and cutter: ###');
    TRACE(ml__debug(ml, 0, 20, problem));
    TRACE(m2d__debug(problem));
    stacksBefore = solveStack.length;
    changes = 0;
    cutLoop();
    term.timeEnd('-> cut_loop ' + loops);
    term.log('   - end cutter outer loop', loops, ', removed:', solveStack.length - stacksBefore, ' vars, total changes:', changes, ', emptyDomain =', emptyDomain, 'once=', once);
    ++loops;
  } while (!emptyDomain && changes && !once && !requestAnotherCycle);

  TRACE('## exit cutter', emptyDomain ? '[there was an empty domain]' : requestAnotherCycle ? '[explicitly requesting another cycle]' : loops > 1 ? '[it might not be done]' : '[it is done]');
  if (emptyDomain) return -1;
  return loops + (requestAnotherCycle ? 1 : 0);

  function somethingChanged() {
    ++changes;
  }

  function readIndex(ml, offset) {
    ASSERT(ml instanceof Uint8Array, 'ml should be a buffer');
    ASSERT(typeof offset === 'number' && offset >= 0 && offset <= ml.length, 'expecting valid offset');
    ASSERT(arguments.length === 2, 'only two args');
    return getAlias(ml_dec16(ml, offset));
  }

  function getMeta(bounty, index, keepBoolyFlags, _debug) {
    ASSERT(typeof index === 'number' && index >= 0 && index <= 0xffff, 'expecting valid index');
    ASSERT(arguments.length === 2 || arguments.length === 3, 'only two or three args');

    if (!isConstant(index)) {
      var meta = bounty_getMeta(bounty, index, _debug);
      if (!keepBoolyFlags) return scrubBoolyFlag(meta);
      return meta;
    }

    return 0;
  }

  function scrubBoolyFlag(meta) {
    return (meta | BOUNTY_FLAG_NOT_BOOLY) ^ BOUNTY_FLAG_NOT_BOOLY;
  }

  function hasFlags(meta, flags) {
    return (meta & flags) === flags;
  }

  function getCounts(bounty, index) {
    ASSERT(typeof index === 'number' && index >= 0 && index <= 0xffff, 'expecting valid index');
    ASSERT(arguments.length === 2, 'no more than two args');
    if (!isConstant(index)) return bounty_getCounts(bounty, index);
    return 0;
  } // ##############


  function cutLoop() {
    TRACE('\n#### - inner cutLoop');
    pc = 0;

    while (pc < ml.length && !emptyDomain && !requestAnotherCycle) {
      var op = ml[pc];
      TRACE(' -- CU pc=' + pc, ', op=', op, ml__opName(op));
      TRACE(' -> op: ' + ml__debug(ml, pc, 1, problem, true));
      ASSERT(ml_validateSkeleton(ml, 'cutLoop'));

      switch (op) {
        case ML_ALL:
          return ml_throw(ml, pc, 'all() should be solved and eliminated');

        case ML_DIFF:
          cut_diff(ml, pc);
          break;

        case ML_DIV:
          pc += SIZEOF_VVV;
          break;

        case ML_IMP:
          cut_imp(ml, pc);
          break;

        case ML_ISALL:
          cut_isall(ml, pc);
          break;

        case ML_ISDIFF:
          cut_isdiff(ml, pc);
          break;

        case ML_ISLT:
          cut_islt(ml, pc);
          break;

        case ML_ISLTE:
          cut_islte(ml, pc);
          break;

        case ML_ISNALL:
          cut_isnall(ml, pc);
          break;

        case ML_ISSAME:
          cut_issame(ml, pc);
          break;

        case ML_ISSOME:
          cut_issome(ml, pc);
          break;

        case ML_ISNONE:
          TRACE('(skipped) issome/isnone', pc);
          var nlen = ml_dec16(ml, pc + 1);
          pc += SIZEOF_C + nlen * 2 + 2;
          break;

        case ML_LT:
          cut_lt(ml, pc);
          break;

        case ML_LTE:
          cut_lte(ml, pc);
          break;

        case ML_MINUS:
          pc += SIZEOF_VVV;
          break;

        case ML_NALL:
          cut_nall(ml, pc);
          break;

        case ML_NIMP:
          TRACE('(skipped) nimp', pc);
          pc += SIZEOF_C_2;
          break;

        case ML_NONE:
          return ml_throw(ml, pc, 'nors should be solved and eliminated');

        case ML_PRODUCT:
          TRACE('(skipped) product', pc);
          var plen = ml_dec16(ml, pc + 1);
          pc += SIZEOF_C + plen * 2 + 2;
          break;

        case ML_SAME:
          return ml_throw(ml, pc, 'eqs should be aliased and eliminated');

        case ML_SOME:
          cut_some(ml, pc);
          break;

        case ML_SUM:
          cut_sum(ml, pc);
          break;

        case ML_XOR:
          cut_xor(ml, pc);
          break;

        case ML_XNOR:
          cut_xnor(ml, pc);
          break;

        case ML_START:
          if (pc !== 0) return ml_throw(ml, pc, ' ! compiler problem @');
          ++pc;
          break;

        case ML_STOP:
          return;

        case ML_NOBOOL:
        case ML_NOLEAF:
          pc += SIZEOF_V;
          break;

        case ML_JMP:
          cut_moveTo(ml, pc, SIZEOF_V + ml_dec16(ml, pc + 1));
          break;

        case ML_JMP32:
          cut_moveTo(ml, pc, SIZEOF_W + ml_dec32(ml, pc + 1));
          break;

        case ML_NOOP:
          cut_moveTo(ml, pc, 1);
          break;

        case ML_NOOP2:
          cut_moveTo(ml, pc, 2);
          break;

        case ML_NOOP3:
          cut_moveTo(ml, pc, 3);
          break;

        case ML_NOOP4:
          cut_moveTo(ml, pc, 4);
          break;

        default:
          getTerm().error('(cut) unknown op', pc, ' at', pc);
          ml_throw(ml, pc, '(cut) unknown op');
      }
    }

    if (emptyDomain) {
      TRACE('Ended up with an empty domain');
      return;
    }

    if (requestAnotherCycle) {
      TRACE('Stopped cutloop prematurely because another minimizer cycle was requested');
      return;
    }

    TRACE('the implicit end; ml desynced');
    THROW('ML OOB');
  }

  function cut_diff(ml, offset) {
    var argCount = ml_dec16(ml, offset + 1);
    TRACE(' ! cut_diff;', argCount, 'args');
    var indexA = readIndex(ml, offset + OFFSET_C_A);
    var countsA = getCounts(bounty, indexA);

    if (countsA > 1 && countsA < BOUNTY_MAX_OFFSETS_TO_TRACK) {
      // Search all counts for a second SOME
      if (desubset_diff(ml, offset, argCount, indexA, countsA)) return;
    }

    if (argCount !== 2) {
      TRACE(' - did not have 2 args, bailing for now');
      pc += SIZEOF_C + argCount * 2;
      return;
    } // For the remainder, these are NEQ cuts (diff[2])


    var indexB = readIndex(ml, offset + OFFSET_C_B);
    var countsB = getCounts(bounty, indexB);
    TRACE(' - diff:', indexA, '!=', indexB, '::', domain__debug(getDomain(indexA, true)), '!=', domain__debug(getDomain(indexB, true)));
    ASSERT(!countsA || !domain_isSolved(getDomain(indexA, true)), 'if it has counts it shouldnt be solved', countsA, indexA, domain__debug(getDomain(indexA, true)));
    ASSERT(!countsB || !domain_isSolved(getDomain(indexB, true)), 'if it has counts it shouldnt be solved', countsB, indexB, domain__debug(getDomain(indexB, true)));
    TRACE('  - counts:', countsA, countsB, ', meta:', bounty__debugMeta(bounty, indexA), bounty__debugMeta(bounty, indexB));

    if (indexA === indexB) {
      TRACE(' - index A == B, redirecting to minimizer');
      requestAnotherCycle = true;
      return;
    }

    if (countsA === 1) {
      return leaf_diff_pair(ml, offset, indexA, indexB, indexA, indexB);
    }

    if (countsB === 1) {
      return leaf_diff_pair(ml, offset, indexB, indexA, indexA, indexB);
    }

    var TRICK_INV_DIFF_FLAGS = BOUNTY_FLAG_LTE_LHS | BOUNTY_FLAG_LTE_RHS | BOUNTY_FLAG_SOME | BOUNTY_FLAG_NALL | BOUNTY_FLAG_IMP_LHS | BOUNTY_FLAG_IMP_RHS;

    if (countsA > 1 && countsA <= BOUNTY_MAX_OFFSETS_TO_TRACK) {
      var metaA = getMeta(bounty, indexA); // Check if it has any targeted ops, then check if it has no other stuff

      var hasGoodOps = (metaA & TRICK_INV_DIFF_FLAGS) > 0;
      var hasBadOps = (metaA | TRICK_INV_DIFF_FLAGS | BOUNTY_FLAG_DIFF) ^ (TRICK_INV_DIFF_FLAGS | BOUNTY_FLAG_DIFF);
      TRACE('  - has good:', hasGoodOps, ', hasBad:', hasBadOps); // TODO: why are we checking diff here? shouldnt that have been done above? and why not checking that below?

      if (hasFlags(metaA, BOUNTY_FLAG_DIFF) && hasGoodOps && !hasBadOps) {
        if (trick_diff_elimination(offset, indexA, countsA, indexB)) return;
      }

      if (hasFlags(metaA, BOUNTY_FLAG_DIFF | BOUNTY_FLAG_XOR)) {
        if (trick_diff_xor(ml, offset, indexA, countsA, indexB)) return;
      }

      if (trick_diff_alias(indexA, indexB, countsA)) return;
    }

    if (countsB > 1 && countsB <= BOUNTY_MAX_OFFSETS_TO_TRACK) {
      var metaB = getMeta(bounty, indexB); // First remove the booly flag, then check if it has any targeted ops, then check if it has no other stuff

      var _hasGoodOps = (metaB & TRICK_INV_DIFF_FLAGS) > 0;

      var _hasBadOps = (metaB | TRICK_INV_DIFF_FLAGS | BOUNTY_FLAG_DIFF) ^ (TRICK_INV_DIFF_FLAGS | BOUNTY_FLAG_DIFF);

      TRACE('  - has good:', _hasGoodOps, ', hasBad:', _hasBadOps);

      if (_hasGoodOps && !_hasBadOps) {
        if (trick_diff_elimination(offset, indexB, countsB, indexA)) return;
      }

      if (hasFlags(metaB, BOUNTY_FLAG_DIFF | BOUNTY_FLAG_XOR)) {
        if (trick_diff_xor(ml, offset, indexB, countsB, indexA)) return;
      }

      if (trick_diff_alias(indexB, indexA, countsB)) return;
      var A = getDomain(indexA, true);
      var B = getDomain(indexB, true);

      if (domain_isBoolyPair(A) && A === B) {
        TRACE(' - A and B are booly pair and equal so turn this DIFF into a XOR');
        TRACE_MORPH('A:[00xx] != B:[00xx]', 'A ^ B');
        ml_enc8(ml, offset, ML_XOR);
        bounty_markVar(bounty, indexA);
        bounty_markVar(bounty, indexB);
        somethingChanged();
        return;
      }
    }

    TRACE(' - cut_diff changed nothing');
    pc += SIZEOF_C_2;
  }

  function cut_imp(ml, offset) {
    var indexA = readIndex(ml, offset + OFFSET_C_A);
    var indexB = readIndex(ml, offset + OFFSET_C_B);
    var A = getDomain(indexA, true);
    var B = getDomain(indexB, true);
    var countsA = getCounts(bounty, indexA);
    var countsB = getCounts(bounty, indexB);
    TRACE(' ! cut_imp;', indexA, '->', indexB, ', ', domain__debug(A), '->', domain__debug(B));
    TRACE('  - counts:', countsA, '->', countsB, ', meta:', bounty__debugMeta(bounty, indexA), '->', bounty__debugMeta(bounty, indexB));

    if (indexA === indexB) {
      TRACE(' - index A == B, redirecting to minimizer');
      requestAnotherCycle = true;
      return;
    }

    if (!domain_isBooly(A) || domain_hasNoZero(B)) {
      TRACE(' - this imp is already solved, bouncing back to minimizer');
      requestAnotherCycle = true;
      return false;
    }

    if (countsA === 1) {
      return leaf_imp(ml, offset, indexA, indexB, true);
    }

    if (countsB === 1) {
      return leaf_imp(ml, offset, indexA, indexB, false);
    }

    if (countsA > 0) {
      var metaA = getMeta(bounty, indexA);
      ASSERT(metaA & BOUNTY_FLAG_IMP_LHS, 'should be');

      if (metaA === BOUNTY_FLAG_IMP_LHS) {
        if (trick_only_implhs_leaf(ml, indexA, countsA)) return;
      }

      if (metaA === BOUNTY_FLAG_NALL || metaA === (BOUNTY_FLAG_NALL | BOUNTY_FLAG_IMP_LHS)) {
        if (trick_implhs_nall_leaf(ml, indexA)) return;
      }

      if (countsA === 2) {
        if (metaA === (BOUNTY_FLAG_IMP_LHS | BOUNTY_FLAG_SOME)) {
          if (trick_implhs_some_leaf(ml, offset, indexA, countsA)) return;
        }
      }

      if (hasFlags(metaA, BOUNTY_FLAG_ISALL_RESULT)) {
        // This trick has isall subsume the lte, so no need for R to be leaf
        if (trick_implhs_isall_2shared(ml, offset, indexA, countsA)) return; // This trick requires R to be leaf

        if (countsA === 2) {
          if (trick_isall_implhs_1shared(ml, offset, indexA, countsA)) return;
        }
      }

      if (countsA >= 3) {
        if (metaA === (BOUNTY_FLAG_SOME | BOUNTY_FLAG_NALL | BOUNTY_FLAG_IMP_LHS)) {
          if (trick_implhs_nalls_some(indexA, countsA)) return;
        }

        if (metaA === (BOUNTY_FLAG_SOME | BOUNTY_FLAG_NALL | BOUNTY_FLAG_IMP_LHS | BOUNTY_FLAG_IMP_RHS)) {
          if (trick_impboth_nall_some(indexA, countsA)) return;
        }
      }
    }

    if (domain_isBool(A) && domain_isBool(B)) {
      if (countsB === 2) {
        var metaB = getMeta(bounty, indexB, true); // Keep booly flags

        if (metaB === (BOUNTY_FLAG_IMP_RHS | BOUNTY_FLAG_ISALL_RESULT)) {
          if (trick_imprhs_isall_entry(indexB, offset, countsB, indexA)) return;
        }
      }
    }

    TRACE(' - cut_imp did nothing');
    pc += SIZEOF_C_2;
  }

  function cut_isall(ml, offset) {
    var argCount = ml_dec16(ml, offset + 1);
    var argsOffset = offset + SIZEOF_C;
    var opSize = SIZEOF_C + argCount * 2 + 2;
    var indexR = readIndex(ml, argsOffset + argCount * 2);
    var countsR = getCounts(bounty, indexR);
    TRACE(' ! cut_isall; R=', indexR, ', counts:', countsR, ', metaR:', bounty__debugMeta(bounty, indexR));
    ASSERT(!countsR || !domain_isSolved(getDomain(indexR, true)), 'if it has counts it shouldnt be solved', countsR, indexR, domain__debug(getDomain(indexR, true)));

    if (countsR > 0 && countsR < BOUNTY_MAX_OFFSETS_TO_TRACK) {
      if (countsR === 1) {
        // When R is a leaf, the isall args are not bound by it nor the reifier so they are free
        return leaf_isall(ml, offset, argCount, indexR);
      }

      var metaR = getMeta(bounty, indexR);

      if (metaR === (BOUNTY_FLAG_ISALL_RESULT | BOUNTY_FLAG_ISALL_ARG)) {
        if (leaf_isall_arg_result(ml, indexR, countsR)) return;
      }

      if (countsR === 2) {
        if (metaR === (BOUNTY_FLAG_NALL | BOUNTY_FLAG_ISALL_RESULT)) {
          if (trick_isall_nall_2shared(ml, indexR, offset, countsR)) return;
        }
      }

      if (metaR === (BOUNTY_FLAG_NALL | BOUNTY_FLAG_ISALL_RESULT)) {
        if (trick_isall_nall_1shared(ml, indexR, offset, countsR)) return;
      }
    }

    TRACE('   cut_isall changed nothing');
    pc += opSize;
  }

  function cut_isdiff(ml, offset) {
    var argCount = ml_dec16(ml, offset + 1);
    var indexR = readIndex(ml, offset + SIZEOF_C + argCount * 2);
    TRACE(' ! cut_isdiff; ', indexR, '::', domain__debug(getDomain(indexR, true)), ', args:', argCount);

    if (argCount !== 2) {
      TRACE(' - argCount=', argCount, ', bailing because it is not 2');
      pc = offset + SIZEOF_C + argCount * 2 + 2;
      return;
    }

    var indexA = readIndex(ml, offset + OFFSET_C_A);
    var indexB = readIndex(ml, offset + OFFSET_C_B);
    var countsA = getCounts(bounty, indexA);
    var countsB = getCounts(bounty, indexB);
    var countsR = getCounts(bounty, indexR);
    TRACE(' -', indexR, '=', indexA, '!=?', indexB, '::', domain__debug(getDomain(indexR, true)), '=', domain__debug(getDomain(indexA, true)), '!=?', domain__debug(getDomain(indexB, true)));
    ASSERT(!countsA || !domain_isSolved(getDomain(indexA, true)), 'if it has counts it shouldnt be solved', countsA, indexA, domain__debug(getDomain(indexA, true)));
    ASSERT(!countsB || !domain_isSolved(getDomain(indexB, true)), 'if it has counts it shouldnt be solved', countsB, indexB, domain__debug(getDomain(indexB, true)));
    ASSERT(!countsR || !domain_isSolved(getDomain(indexR, true)), 'if it has counts it shouldnt be solved', countsR, indexR, domain__debug(getDomain(indexR, true)));
    TRACE('  - counts:', countsR, countsA, countsB, ', meta:', bounty__debugMeta(bounty, indexR), '=', bounty__debugMeta(bounty, indexA), '!=?', bounty__debugMeta(bounty, indexB));

    if (countsR === 1) {
      return leaf_isdiff(ml, offset, indexA, indexB, indexR, indexR);
    }

    if (countsA === 1) {
      ASSERT(!domain_isSolved(getDomain(indexA, true)), 'A cannot be solved (bounty ignores constants so count would be 0)');

      if (canCutIsdiffForArg(indexA, indexB, indexR)) {
        return leaf_isdiff(ml, offset, indexA, indexB, indexR, indexA);
      }
    }

    if (countsB === 1) {
      // Not covered, kept here just in case the above assertion doesnt hold in prod
      ASSERT(!domain_isSolved(getDomain(indexB, true)), 'B cannot be solved (bounty ignores constants so count would be 0)');

      if (canCutIsdiffForArg(indexB, indexA, indexR)) {
        return leaf_isdiff(ml, offset, indexA, indexB, indexR, indexB);
      }
    }

    var R = getDomain(indexR, true);
    var A = getDomain(indexA, true);
    var B = getDomain(indexB, true);

    if (domain_isBoolyPair(R)) {
      if (domain_isBoolyPair(A) && domain_isSolved(B)) {
        // R:[00yy] = A:[00xx] !=? 0/x
        if (domain_isZero(B)) {
          TRACE_MORPH('R = A !=? 0', '!(R ^ A)');
          ml_cr2c2(ml, offset, 2, ML_XNOR, indexA, indexR);
          bounty_markVar(bounty, indexA);
          bounty_markVar(bounty, indexB);
          bounty_markVar(bounty, indexR);
          somethingChanged();
          return;
        }

        if (domain_max(A) === domain_getValue(B)) {
          // Must confirm A contains B because it may in some edge cases not
          TRACE_MORPH('R = A:[00xx] !=? x', 'R ^ A');
          ml_cr2c2(ml, offset, 2, ML_XOR, indexA, indexR);
          bounty_markVar(bounty, indexA);
          bounty_markVar(bounty, indexB);
          bounty_markVar(bounty, indexR);
          somethingChanged();
          return;
        }
      }

      if (domain_isSolved(A) && domain_isBoolyPair(B)) {
        // R:[00yy] = 0/x !=? A:[00xx]
        if (domain_isZero(A)) {
          TRACE_MORPH('R = 0 !=? B', '!(R ^ B)');
          ml_cr2c2(ml, offset, 2, ML_XNOR, indexB, indexR);
          bounty_markVar(bounty, indexA);
          bounty_markVar(bounty, indexB);
          bounty_markVar(bounty, indexR);
          somethingChanged();
          return;
        }

        if (domain_max(B) === domain_getValue(A)) {
          // Must confirm B contains A because it may in some edge cases not
          TRACE_MORPH('R = x !=? B:[00xx]', 'R ^ B');
          ml_cr2c2(ml, offset, 2, ML_XOR, indexB, indexR);
          bounty_markVar(bounty, indexA);
          bounty_markVar(bounty, indexB);
          bounty_markVar(bounty, indexR);
          somethingChanged();
          return;
        }
      }
    }

    TRACE(' - cut_isdiff changed nothing');
    pc = offset + SIZEOF_CR_2;
  }

  function canCutIsdiffForArg(indexL, indexO, indexR) {
    TRACE('   - canCutIsdiffForArg;', indexL, indexO, indexR, '->', domain__debug(getDomain(indexR, true)), '=', domain__debug(getDomain(indexL, true)), '!=?', domain__debug(getDomain(indexO, true))); // An isdiff with 2 args can only be leaf-cut on an arg if the leaf can represent all outcomes
    // so if C is solved, solve as SAME or DIFF.
    // otherwise make sure the leaf contains all vars of the other var and at least one var that's not in there
    // as long as that's impossible we can't cut it without implicitly forcing vars
    // first check whether R is booly-solved, this would mean fewer values to check

    var R = getDomain(indexR, true);

    if (domain_hasNoZero(R)) {
      TRACE('    - R=0 and size(L)>2 so cuttable'); // L contains at least two values so regardless of the state of O, L can fulfill !=

      ASSERT(domain_size(L) >= 2, 'see?');
      return true;
    } // R=1 or R=booly is more involved because we at least
    // need to know whether L contains all values in O


    var L = getDomain(indexL, true);
    var O = getDomain(indexO, true);
    var LO = domain_intersection(L, O); // <-- this tells us that

    TRACE('    - LO:', domain__debug(LO));

    if (domain_isZero(R)) {
      // Only cut if we are certain L can represent eq in any way O solves
      if (!LO) {
        TRACE('    - R>=1 and A contains no value in B so reject'); // No values in L and O match so reject

        setDomain(indexL, domain_createEmpty(), false, true);
        return false;
      }

      if (LO === O) {
        TRACE('    - R>=1 and A contains all values in B so cuttable'); // This means L contains all values in O (and maybe more, dont care)
        // which means L can uphold the eq for any value of O

        return true;
      }

      TRACE('    - R>=1 and A contains some but not all B so not cuttable, yet'); // There's no guarantee O solves to a value in L so we cant cut safely

      return true;
    }

    TRACE('    - R unresolved, cuttable if L contains all values in O and then some;', LO === O, LO !== L, 'so:', LO === O && LO !== L); // We dont know R so L should contain all values in O (LO==O) and at least
    // one value not in O (LO != O), to consider this a safe cut. otherwise dont.

    return LO === O && LO !== L;
  }

  function cut_islt(ml, offset) {
    var indexA = readIndex(ml, offset + 1);
    var indexB = readIndex(ml, offset + 3);
    var indexR = readIndex(ml, offset + 5);
    var countsA = getCounts(bounty, indexA);
    var countsB = getCounts(bounty, indexB);
    var countsR = getCounts(bounty, indexR);
    TRACE(' ! cut_islt; ', indexR, '=', indexA, '<?', indexB, '::', domain__debug(getDomain(indexR, true)), '=', domain__debug(getDomain(indexA, true)), '<?', domain__debug(getDomain(indexB, true)));
    ASSERT(!countsA || !domain_isSolved(getDomain(indexA, true)), 'if it has counts it shouldnt be solved', countsA, indexA, domain__debug(getDomain(indexA, true)));
    ASSERT(!countsB || !domain_isSolved(getDomain(indexB, true)), 'if it has counts it shouldnt be solved', countsB, indexB, domain__debug(getDomain(indexB, true)));
    ASSERT(!countsR || !domain_isSolved(getDomain(indexR, true)), 'if it has counts it shouldnt be solved', countsR, indexR, domain__debug(getDomain(indexR, true)));
    TRACE('  - counts:', countsR, countsA, countsB, ', meta:', bounty__debugMeta(bounty, indexR), '=', bounty__debugMeta(bounty, indexA), '<?', bounty__debugMeta(bounty, indexB));

    if (countsR === 1) {
      return leaf_islt(ml, offset, indexA, indexB, indexR, indexR);
    }

    if (countsA === 1) {
      if (canCutIsltForArg(indexA, indexB, indexR, indexA, indexB)) {
        return leaf_islt(ml, offset, indexA, indexB, indexR, indexA);
      }
    }

    if (countsB === 1) {
      if (canCutIsltForArg(indexB, indexA, indexR, indexA, indexB)) {
        return leaf_islt(ml, offset, indexA, indexB, indexR, indexB);
      }
    }

    TRACE(' - cut_islt changed nothing');
    pc = offset + SIZEOF_VVV;
  }

  function canCutIsltForArg(indexL, indexO, indexR, indexA, indexB) {
    TRACE('   - canCutIsltForArg;', indexL, indexO, indexR, '->', domain__debug(getDomain(indexR, true)), '=', domain__debug(getDomain(indexA, true)), '<?', domain__debug(getDomain(indexB, true))); // An islt can only be leaf-cut on an arg if the leaf can represent all outcomes
    // so if C is solved, solve as SAME or DIFF.
    // otherwise make sure the leaf contains all vars of the other var and at least one var that's not in there
    // as long as that's impossible we can't cut it without implicitly forcing vars
    // keep in mind A and B are ordered and cant be swapped
    // first check whether R is booly-solved, this would mean fewer values to check

    var A = getDomain(indexA, true);
    var B = getDomain(indexB, true);
    var R = getDomain(indexR, true);

    if (domain_hasNoZero(R)) {
      TRACE('   - R>0'); // If L is A, O must have at least one value below min(B). otherwise it must have at least one value > max(A).

      if (indexL === indexA) return domain_min(A) < domain_min(B);
      return domain_max(B) > domain_max(A);
    }

    if (domain_isZero(R)) {
      TRACE('   - R=0'); // If L is A, O must have at least one value >= min(B). otherwise it must have at least one value <= max(A).

      if (indexL === indexA) return domain_min(A) >= domain_min(B);
      return domain_max(B) <= domain_max(A);
    } // R unresolved. O must have at least both values to represent R=0 and R>=1


    if (indexL === indexA) {
      TRACE('   - R unresolved, L=A', domain_min(A) < domain_min(B), domain_max(A) >= domain_max(B)); // L must contain a value < min(B) and a value >= max(B)

      return domain_min(A) < domain_min(B) && domain_max(A) >= domain_max(B);
    }

    TRACE('   - R unresolved, L=B', domain_max(B), '>', domain_max(A), '->', domain_max(B) > domain_max(A), domain_min(B), '<=', domain_min(A), '->', domain_min(B) <= domain_min(A)); // L is B, L must contain one value above max(A) and one value <= min(A)

    return domain_max(B) > domain_max(A) && domain_min(B) <= domain_min(A);
  }

  function cut_islte(ml, offset) {
    var indexA = readIndex(ml, offset + 1);
    var indexB = readIndex(ml, offset + 3);
    var indexR = readIndex(ml, offset + 5);
    var countsA = getCounts(bounty, indexA);
    var countsB = getCounts(bounty, indexB);
    var countsR = getCounts(bounty, indexR);
    TRACE(' ! cut_islte; ', indexR, '=', indexA, '<=?', indexB, '::', domain__debug(getDomain(indexR, true)), '=', domain__debug(getDomain(indexA, true)), '<=?', domain__debug(getDomain(indexB, true)));
    ASSERT(!countsA || !domain_isSolved(getDomain(indexA, true)), 'if it has counts it shouldnt be solved', countsA, indexA, domain__debug(getDomain(indexA, true)));
    ASSERT(!countsB || !domain_isSolved(getDomain(indexB, true)), 'if it has counts it shouldnt be solved', countsB, indexB, domain__debug(getDomain(indexB, true)));
    ASSERT(!countsR || !domain_isSolved(getDomain(indexR, true)), 'if it has counts it shouldnt be solved', countsR, indexR, domain__debug(getDomain(indexR, true)));
    TRACE('  - counts:', countsR, countsA, countsB, ', meta:', bounty__debugMeta(bounty, indexR), '=', bounty__debugMeta(bounty, indexA), '<=?', bounty__debugMeta(bounty, indexB));
    var R = getDomain(indexR, true);

    if (!domain_isBooly(R)) {
      TRACE(' - R is already booly solved, requesting another minifier sweep, bailing');
      requestAnotherCycle = true;
      return;
    }

    if (countsR === 1) {
      return leaf_islte(ml, offset, indexA, indexB, indexR, indexR);
    }

    var A = getDomain(indexA, true);
    var B = getDomain(indexB, true);

    if (countsA === 1) {
      if (canCutIslteForArg(indexA, indexB, indexA, indexB, A, B)) {
        return leaf_islte(ml, offset, indexA, indexB, indexR, indexA);
      }
    }

    if (countsB === 1) {
      if (canCutIslteForArg(indexB, indexA, indexA, indexB, A, B)) {
        return leaf_islte(ml, offset, indexA, indexB, indexR, indexB);
      }
    }

    if (countsR > 0 && countsR < BOUNTY_MAX_OFFSETS_TO_TRACK) {
      if (domain_isSolved(A)) {
        // R = x <=? B
        var metaR = getMeta(bounty, indexR);

        if (hasFlags(metaR, BOUNTY_FLAG_IMP_RHS)) {
          var metaB = getMeta(bounty, indexB);

          if (hasFlags(metaB, BOUNTY_FLAG_IMP_LHS)) {
            if (trick_imp_islte_c_v(offset, indexR, indexA, indexB, countsR)) return;
          }
        }
      }

      if (domain_isSolved(B)) {
        // R = A <=? x
        var _metaR = getMeta(bounty, indexR);

        if (hasFlags(_metaR, BOUNTY_FLAG_IMP_RHS)) {
          var metaA = getMeta(bounty, indexA);

          if (hasFlags(metaA, BOUNTY_FLAG_IMP_LHS)) {
            if (trick_imp_islte_v_c(offset, indexR, indexA, indexB, countsR)) return;
          }
        }
      }
    }

    TRACE(' - cut_islte changed nothing');
    pc = offset + SIZEOF_VVV;
  }

  function canCutIslteForArg(indexL, indexO, indexA, indexB, A, B) {
    TRACE('   - canCutIslteForArg;', indexL, indexO, domain__debug(getDomain(indexA, true)), '<=?', domain__debug(getDomain(indexB, true))); // An islte can only be leaf-cut on an arg if the leaf can represent all outcomes
    // so if C is solved, solve as SAME or DIFF.
    // otherwise make sure the leaf contains all vars of the other var and at least one var that's not in there
    // as long as that's impossible we can't cut it without implicitly forcing vars
    // keep in mind A and B are ordered and cant be swapped
    // R unresolved. O must have at least both values to represent R=0 and R>=1

    if (indexL === indexA) {
      TRACE('   - L=A', domain_min(A) <= domain_min(B), domain_max(A) > domain_max(B)); // L must contain a value <= min(B) and a value > max(B)

      return domain_min(A) <= domain_min(B) && domain_max(A) > domain_max(B);
    }

    TRACE('   - L=B', domain_max(B), '>=', domain_max(A), '->', domain_max(B) >= domain_max(A), domain_min(B), '<', domain_min(A), '->', domain_min(B) < domain_min(A)); // L is B, L must contain one value gte max(A) and one value below min(A)

    return domain_max(B) >= domain_max(A) && domain_min(B) < domain_min(A);
  }

  function cut_isnall(ml, offset) {
    var argCount = ml_dec16(ml, offset + 1);
    var argsOffset = offset + SIZEOF_C;
    var opSize = SIZEOF_C + argCount * 2 + 2;
    var indexR = readIndex(ml, argsOffset + argCount * 2);
    var countsR = getCounts(bounty, indexR);
    TRACE(' ! cut_isnall; R=', indexR);
    ASSERT(!countsR || !domain_isSolved(getDomain(indexR, true)), 'if it has counts it shouldnt be solved', countsR, indexR, domain__debug(getDomain(indexR, true)));

    if (countsR === 1) {
      return leaf_isnall(ml, offset, argCount, indexR, countsR);
    }

    pc += opSize;
  }

  function cut_issame(ml, offset) {
    var argCount = ml_dec16(ml, offset + 1);
    TRACE(' ! cut_issame');

    if (argCount !== 2) {
      TRACE(' - argCount != 2 so bailing, for now');
      pc = offset + SIZEOF_C + argCount * 2 + 2;
      return;
    }

    var indexA = readIndex(ml, offset + OFFSET_C_A);
    var indexB = readIndex(ml, offset + OFFSET_C_B);
    var indexR = readIndex(ml, offset + OFFSET_C_C);
    var countsA = getCounts(bounty, indexA);
    var countsB = getCounts(bounty, indexB);
    var countsR = getCounts(bounty, indexR);
    TRACE(' - cut_issame; ', indexR, '=', indexA, '==?', indexB, '::', domain__debug(getDomain(indexR, true)), '=', domain__debug(getDomain(indexA, true)), '==?', domain__debug(getDomain(indexB, true)));
    ASSERT(!countsA || !domain_isSolved(getDomain(indexA, true)), 'if it has counts it shouldnt be solved', countsA, indexA, domain__debug(getDomain(indexA, true)));
    ASSERT(!countsB || !domain_isSolved(getDomain(indexB, true)), 'if it has counts it shouldnt be solved', countsB, indexB, domain__debug(getDomain(indexB, true)));
    ASSERT(!countsR || !domain_isSolved(getDomain(indexR, true)), 'if it has counts it shouldnt be solved', countsR, indexR, domain__debug(getDomain(indexR, true)));
    TRACE('  - counts:', countsR, countsA, countsB, ', meta:', bounty__debugMeta(bounty, indexR), '=', bounty__debugMeta(bounty, indexA), '==?', bounty__debugMeta(bounty, indexB));

    if (countsR === 1) {
      return leaf_issame(ml, offset, indexA, indexB, indexR, indexR);
    }

    if (countsA === 1) {
      ASSERT(!domain_isSolved(getDomain(indexA, true)), 'A cannot be solved (bounty ignores constants so count would be 0)');

      if (canCutIssameForArg(indexA, indexB, indexR)) {
        return leaf_issame(ml, offset, indexA, indexB, indexR, indexA);
      }
    }

    if (countsB === 1) {
      // Not covered, kept here just in case the above assertion doesnt hold in prod
      ASSERT(!domain_isSolved(getDomain(indexB, true)), 'B cannot be solved (bounty ignores constants so count would be 0)');

      if (canCutIssameForArg(indexB, indexA, indexR)) {
        return leaf_issame(ml, offset, indexA, indexB, indexR, indexB);
      }
    }

    TRACE(' - no change from cut_issame');
    ASSERT(ml_dec16(ml, offset + 1) === 2, 'should have 2 args');
    pc = offset + SIZEOF_CR_2;
  }

  function canCutIssameForArg(indexL, indexO, indexR) {
    TRACE('   - canCutIssameForArg;', indexL, indexO, indexR, '->', domain__debug(getDomain(indexR, true)), '=', domain__debug(getDomain(indexL, true)), '==?', domain__debug(getDomain(indexO, true))); // An issame can only be leaf-cut on an arg if the leaf can represent all outcomes
    // so if C is solved, solve as SAME or DIFF.
    // otherwise make sure the leaf contains all vars of the other var and at least one var that's not in there
    // as long as that's impossible we can't cut it without implicitly forcing vars
    // first check whether R is booly-solved, this would mean fewer values to check

    var R = getDomain(indexR, true);

    if (domain_isZero(R)) {
      TRACE('    - R=0 and size(L)>2 so cuttable'); // L contains at least two values so regardless of the state of O, L can fulfill !=

      ASSERT(domain_size(L) >= 2, 'see?');
      return true;
    } // R=1 or R=booly is more involved because we at least
    // need to know whether L contains all values in O


    var L = getDomain(indexL, true);
    var O = getDomain(indexO, true);
    var LO = domain_intersection(L, O); // <-- this tells us that

    TRACE('    - LO:', domain__debug(LO));

    if (domain_hasNoZero(R)) {
      // Only cut if we are certain L can represent eq in any way O solves
      if (!LO) {
        TRACE('    - R>=1 and A contains no value in B so reject'); // No values in L and O match so reject

        setDomain(indexL, domain_createEmpty(), false, true);
        return false;
      }

      if (LO === O) {
        TRACE('    - R>=1 and A contains all values in B so cuttable'); // This means L contains all values in O (and maybe more, dont care)
        // which means L can uphold the eq for any value of O

        return true;
      }

      TRACE('    - R>=1 and A contains some but not all B so not cuttable, yet'); // There's no guarantee O solves to a value in L so we cant cut safely

      return true;
    }

    TRACE('    - R unresolved, cuttable if L contains all values in O and then some;', LO === O, LO !== L, 'so:', LO === O && LO !== L); // We dont know R so L should contain all values in O (LO==O) and at least
    // one value not in O (LO != O), to consider this a safe cut. otherwise dont.

    return LO === O && LO !== L;
  }

  function cut_issome(ml, offset) {
    var argCount = ml_dec16(ml, offset + 1);
    var argsOffset = offset + SIZEOF_C;
    var opSize = SIZEOF_C + argCount * 2 + 2;
    var indexR = readIndex(ml, argsOffset + argCount * 2);
    var countsR = getCounts(bounty, indexR);
    TRACE(' ! cut_issome; R=', indexR);

    if (countsR === 1) {
      return leaf_issome(ml, offset, indexR, argCount);
    }

    for (var i = 0; i < argCount; ++i) {
      var index = readIndex(ml, offset + SIZEOF_C + i * 2);
      var A = getDomain(index, true);

      if (domain_isZero(A)) {
        TRACE(' - some has zeroes, requesting minimizer to remove them');
        requestAnotherCycle = true; // Minimizer should eliminate these

        break;
      }
    }

    TRACE(' - cut_issome did not change anything');
    pc += opSize;
  }

  function cut_lt(ml, offset) {
    var indexA = readIndex(ml, offset + OFFSET_C_A);
    var indexB = readIndex(ml, offset + OFFSET_C_B);
    var countsA = getCounts(bounty, indexA);
    var countsB = getCounts(bounty, indexB);
    TRACE(' ! cut_lt; ', indexA, '<', indexB, '::', domain__debug(getDomain(indexA, true)), '<', domain__debug(getDomain(indexB, true)));
    ASSERT(!countsA || !domain_isSolved(getDomain(indexA, true)), 'if it has counts it shouldnt be solved', countsA, indexA, domain__debug(getDomain(indexA, true)));
    ASSERT(!countsB || !domain_isSolved(getDomain(indexB, true)), 'if it has counts it shouldnt be solved', countsB, indexB, domain__debug(getDomain(indexB, true)));
    TRACE('  - counts:', countsA, countsB, ', meta:', bounty__debugMeta(bounty, indexA), '<', bounty__debugMeta(bounty, indexB));

    if (indexA === indexB) {
      TRACE(' - index A == B, redirecting to minimizer');
      requestAnotherCycle = true;
      return;
    }

    if (countsA === 1) {
      return leaf_lt(ml, offset, indexA, indexB, 'lhs');
    }

    if (countsB === 1) {
      return leaf_lt(ml, offset, indexA, indexB, 'rhs');
    }

    TRACE(' - cut_lt did not change anything');
    pc += SIZEOF_C_2;
  }

  function cut_lte(ml, offset) {
    var indexA = readIndex(ml, offset + OFFSET_C_A);
    var indexB = readIndex(ml, offset + OFFSET_C_B);
    var countsA = getCounts(bounty, indexA);
    var countsB = getCounts(bounty, indexB);
    TRACE(' ! cut_lte; ', indexA, '<=', indexB, '::', domain__debug(getDomain(indexA, true)), '<=', domain__debug(getDomain(indexB, true)));
    ASSERT(!countsA || !domain_isSolved(getDomain(indexA, true)), 'if it has counts it shouldnt be solved', countsA, indexA, domain__debug(getDomain(indexA, true)));
    ASSERT(!countsB || !domain_isSolved(getDomain(indexB, true)), 'if it has counts it shouldnt be solved', countsB, indexB, domain__debug(getDomain(indexB, true)));
    TRACE('  - counts:', countsA, '<=', countsB, ', meta:', bounty__debugMeta(bounty, indexA), '<=', bounty__debugMeta(bounty, indexB));

    if (indexA === indexB) {
      TRACE(' - index A == B, redirecting to minimizer');
      requestAnotherCycle = true;
      return;
    }

    if (countsA === 1) {
      if (leaf_lte(ml, offset, indexA, indexB, true)) return;
    }

    if (countsB === 1) {
      if (leaf_lte(ml, offset, indexA, indexB, false)) return;
    }

    if (countsA > 0) {
      var metaA = getMeta(bounty, indexA);

      if (metaA === BOUNTY_FLAG_NALL || metaA === (BOUNTY_FLAG_NALL | BOUNTY_FLAG_LTE_LHS)) {
        if (trick_ltelhs_nall_leaf(ml, indexA, countsA)) return;
      }

      if (metaA === BOUNTY_FLAG_LTE_LHS) {
        if (trick_only_ltelhs_leaf(ml, indexA, countsA)) return;
      }

      if (countsA === 2) {
        if (metaA === (BOUNTY_FLAG_LTE_LHS | BOUNTY_FLAG_SOME)) {
          if (trick_ltelhs_some_leaf(ml, offset, indexA, countsA)) return;
        }
      }

      if (countsA >= 3) {
        if (metaA === (BOUNTY_FLAG_SOME | BOUNTY_FLAG_NALL | BOUNTY_FLAG_LTE_LHS)) {
          if (trick_ltelhs_nalls_some(indexA, countsA)) return;
        }

        if (metaA === (BOUNTY_FLAG_SOME | BOUNTY_FLAG_NALL | BOUNTY_FLAG_LTE_LHS | BOUNTY_FLAG_LTE_RHS)) {
          if (trick_lteboth_nall_some(indexA, countsA)) return;
        }
      }

      if (hasFlags(metaA, BOUNTY_FLAG_ISALL_RESULT)) {
        // In this trick one constraint subsumes the other so no need for A being a leaf
        if (trick_isall_ltelhs_2shared(ml, offset, indexA, countsA)) return; // In this trick A needs to be a leaf

        if (countsA === 2) {
          if (trick_isall_ltelhs_1shared(ml, offset, indexA, countsA)) return;
        }
      }
    }

    if (countsB === 2) {
      var metaB = getMeta(bounty, indexB);

      if (metaB === (BOUNTY_FLAG_LTE_RHS | BOUNTY_FLAG_ISALL_RESULT)) {
        if (trick_isall_lterhs_entry(indexB, offset, countsB)) return;
      }

      if (metaB === (BOUNTY_FLAG_LTE_RHS | BOUNTY_FLAG_ISSAME_RESULT)) {
        if (trick_issame_lterhs(indexB, offset, countsB, indexA)) return;
      }
    }

    TRACE(' - cut_lte changed nothing');
    pc += SIZEOF_C_2;
  }

  function cut_nall(ml, offset) {
    var argCount = ml_dec16(ml, offset + 1);
    TRACE(' ! cut_nall;', argCount, 'args');
    var indexA = readIndex(ml, offset + OFFSET_C_A);
    var countsA = getCounts(bounty, indexA);

    if (countsA > 1 && countsA < BOUNTY_MAX_OFFSETS_TO_TRACK) {
      // Search all counts for a second SOME
      if (desubset_nall(ml, offset, argCount, indexA, countsA)) return;
    }

    if (argCount === 2) {
      if (readIndex(ml, offset + OFFSET_C_A) === readIndex(ml, offset + OFFSET_C_B)) {
        TRACE(' - argcount=2 and A==B, requesting minimzer cycle');
        requestAnotherCycle = true;
        return;
      }
    }

    for (var i = 0; i < argCount; ++i) {
      var index = readIndex(ml, offset + SIZEOF_C + i * 2);
      var counts = getCounts(bounty, index);

      if (counts > 0) {
        var meta = getMeta(bounty, index);

        if (meta === BOUNTY_FLAG_NALL) {
          // Var is only used in nalls. eliminate them all and defer the var
          if (trickNallOnly(index, counts)) return true;
        }
      }
    }

    TRACE(' - cut_nall did not change anything');
    pc += SIZEOF_C + argCount * 2;
  }

  function cut_some(ml, offset) {
    var argCount = ml_dec16(ml, pc + 1);
    TRACE(' ! cut_some;', argCount, 'args');
    var indexA = readIndex(ml, offset + OFFSET_C_A);
    var countsA = getCounts(bounty, indexA);

    if (countsA > 1 && countsA < BOUNTY_MAX_OFFSETS_TO_TRACK) {
      // Search all counts for a second SOME
      if (desubset_some(ml, offset, argCount, indexA, countsA)) return;
    }

    if (argCount === 2) {
      var indexB = readIndex(ml, offset + OFFSET_C_B);

      if (indexA === indexB) {
        TRACE(' - argcount=2 and A==B, requesting minimzer cycle');
        requestAnotherCycle = true;
        return;
      }

      if (countsA === 1) {
        leaf_some_2(ml, offset, indexA, indexB, indexA, indexB);
        return;
      }

      var countsB = getCounts(bounty, indexB);

      if (countsB === 1) {
        leaf_some_2(ml, offset, indexB, indexA, indexA, indexB);
        return;
      }
    }

    var hasZero = false;

    for (var i = 0; i < argCount; ++i) {
      var index = readIndex(ml, offset + SIZEOF_C + i * 2);
      var counts = getCounts(bounty, index);

      if (counts > 0) {
        var meta = getMeta(bounty, index);

        if (meta === BOUNTY_FLAG_SOME) {
          // Var is only used in SOMEs. eliminate them all and defer the var
          if (trickSomeOnly(index, counts)) return true;
        }
      }

      var A = getDomain(index, true);

      if (domain_isZero(A)) {
        hasZero = true;
      }
    }

    if (hasZero) {
      TRACE(' - some has zeroes, requesting minimizer to remove them');
      requestAnotherCycle = true; // Minimizer should eliminate these
    }

    TRACE(' - cut_some changed nothing');
    pc += SIZEOF_C + argCount * 2;
  }

  function cut_sum(ml, offset) {
    var argCount = ml_dec16(ml, offset + 1);
    var argsOffset = offset + SIZEOF_C;
    var opSize = SIZEOF_C + argCount * 2 + 2;
    var indexR = readIndex(ml, argsOffset + argCount * 2);
    var R = getDomain(indexR, true);
    var countsR = getCounts(bounty, indexR);
    TRACE(' ! cut_sum;');
    TRACE('  - index R:', indexR, ', domain:', domain__debug(R), ', argCount:', argCount, ',counts R:', countsR, ', meta R:', bounty__debugMeta(bounty, indexR));
    ASSERT(!countsR || !domain_isSolved(getDomain(indexR, true)), 'if it has counts it shouldnt be solved', countsR, indexR, domain__debug(getDomain(indexR, true)));
    var RisBoolyPair = domain_isBoolyPair(R); // Collect meta data on the args of this sum
    // TODO: should we have a bounty for both constraints and vars?

    var allSumArgsBool = true; // All args [01]? used later

    var allSumArgsBoolyPairs = true; // All args have a zero and one nonzero value?

    var sum = domain_createValue(0);
    var argsMinSum = 0;
    var argsMaxSum = 0;
    var constantValue = 0; // Allow up to one constant larger than 0

    var constantArgIndex = -1;
    var multiConstants = false;

    for (var i = 0; i < argCount; ++i) {
      var index = readIndex(ml, argsOffset + i * 2);
      var domain = getDomain(index, true);
      var minValue = domain_min(domain);
      var maxValue = domain_max(domain);
      sum = domain_plus(sum, domain);
      argsMinSum += minValue;
      argsMaxSum += maxValue; // Let nonBoolNonSolvedDomain = maxValue > 1;

      if (minValue === maxValue) {
        multiConstants = constantArgIndex >= 0;
        constantValue = minValue;
        constantArgIndex = i;
      } else {
        if (!domain_isBoolyPair(domain)) allSumArgsBoolyPairs = false;
        if (!domain_isBool(domain)) allSumArgsBool = false;
      }
    }

    TRACE(' - sum args; min:', argsMinSum, ', max:', argsMaxSum, ', constantValue:', constantValue, ', constant pos:', constantArgIndex, ', sum:', domain__debug(sum));

    if (multiConstants) {
      TRACE(' - multiple constants detected, bailing so minimizer can correct this');
      return;
    } // [0 0 23 23] = [0 1] + [0 0 2 2] + [0 0 20 20]   ->    R = all?(A B C)


    if (RisBoolyPair && allSumArgsBoolyPairs) {
      // This trick is irrelevant of leaf status (this could be part of minimizer)
      TRACE(' - R is a booly and all the args are booly too, checking whether', domain_max(R), '===', argsMaxSum);
      ASSERT(argsMinSum === 0, 'if all are booly argsMinSum should be zero');

      if (domain_max(R) === argsMaxSum) {
        TRACE(' - R is', domain__debug(R), 'and all the args are booly and their argsMaxSum is equal to max(R) so this is actually an isall. morphing sum to isall');
        ml_enc8(ml, offset, ML_ISALL);
        return;
      }
    } // Note: we cant simply eliminate leaf vars because they still constrain
    // the allowed distance between the other variables and if you
    // eliminate this constraint, that limitation is not enforced anymore.
    // so thread carefully.


    if (countsR === 1) {
      // R can only be eliminated if all possible additions between A and B occur in it
      // because in that case it no longer serves as a constraint to force certain distance(s)
      if (sum === domain_intersection(R, sum)) {
        // All possible outcomes of summing any element in the sum args are part of R so
        // R is a leaf and the args aren't bound by it so we can safely remove the sum
        return leaf_sum_result(ml, offset, argCount, indexR);
      } // If R is [0, n-1] and all n args are [0, 1] then rewrite to a NALL


      if (allSumArgsBool && R === domain_createRange(0, argCount - 1)) {
        return trick_sum_to_nall(ml, offset, argCount, indexR);
      } // If R is [1, n] and all n args are [0, 1] then rewrite to a SOME


      if (allSumArgsBool && R === domain_createRange(1, argCount)) {
        return trick_some_sum(ml, offset, argCount, indexR);
      }
    }

    if (countsR >= 2) {
      var metaR = getMeta(bounty, indexR);
      ASSERT(hasFlags(metaR, BOUNTY_FLAG_SUM_RESULT), 'per definition because this is the R in a sum'); // TODO: cant we also do this with counts>2 when R is a bool when ignoring the sum?
      // TOFIX: confirm whether we need allSumArgsBool here, or whether we can lax it a little

      if (allSumArgsBoolyPairs && countsR === 2) {
        // We already confirmed that R is for a sum, so we can strictly compare the meta flags
        // (R = sum(A B C) & (S = R==?3)        ->    S = all?(A B C)
        // (R = sum(A B C) & (S = R==?0)        ->    S = none?(A B C)
        // (R = sum(A B C) & (S = R==?[0 1])    ->    S = nall?(A B C)
        // (R = sum(A B C) & (S = R==?[1 2])    ->    S = some?(A B C)
        if (metaR === (BOUNTY_FLAG_ISSAME_ARG | BOUNTY_FLAG_SUM_RESULT)) {
          if (trick_issame_sum(ml, offset, indexR, countsR, argCount, sum, argsMinSum, argsMaxSum, constantValue, constantArgIndex, allSumArgsBoolyPairs)) return;
        } // (R = sum(A B C) & (S = R!=?3)        ->    S = nall?(A B C)
        // (R = sum(A B C) & (S = R!=?0)        ->    S = some?(A B C)
        // (R = sum(A B C) & (S = R!=?[0 1])    ->    S = all?(A B C)
        // (R = sum(A B C) & (S = R!=?[1 2])    ->    S = none?(A B C)
        // if (metaR === (BOUNTY_FLAG_ISDIFF_ARG | BOUNTY_FLAG_SUM_RESULT)) {
        //  if (trickSumIsdiff(ml, offset, indexR, countsR)) return;
        // }
        // (R = sum(A B C) & (S = R<=?0)        ->    S = none?(A B C)
        // (R = sum(A B C) & (S = R<=?2)        ->    S = nall?(A B C)
        // (R = sum(A B C) & (S = 1<=?R)        ->    S = some?(A B C)
        // (R = sum(A B C) & (S = 3<=?R)        ->    S = all?(A B C)


        if (metaR === (BOUNTY_FLAG_ISLTE_ARG | BOUNTY_FLAG_SUM_RESULT)) {
          if (trick_islte_sum(ml, offset, indexR, countsR, argCount, argsMinSum, argsMaxSum, constantValue, constantArgIndex)) return;
        } // (R = sum(A B C) & (S = R<?1)        ->    S = none?(A B C)
        // (R = sum(A B C) & (S = R<?3)        ->    S = nall?(A B C)
        // (R = sum(A B C) & (S = 0<?R)        ->    S = some?(A B C)
        // (R = sum(A B C) & (S = 2<?R)        ->    S = all?(A B C)
        // if (metaR === (BOUNTY_FLAG_ISLT_ARG | BOUNTY_FLAG_SUM_RESULT)) {
        //  if (trickSumIslt(ml, offset, indexR, countsR)) return;
        // }

      }

      if (countsR === 3 && argCount === 2 && metaR === (BOUNTY_FLAG_ISSAME_ARG | BOUNTY_FLAG_SUM_RESULT)) {
        // TODO: make generic :)
        // R = sum(A B), S = R ==? 1, T = R ==? 2    ->    S = A !=? B, T = all?(A B)
        if (trick_issame_issame_sum(ml, offset, indexR, countsR, sum, argCount)) return;
      }

      if (countsR < BOUNTY_MAX_OFFSETS_TO_TRACK) {
        // If R is only used as a booly and (this) sum result, the actual result is irrelevant: only zero or not zero
        // in that case we only want to know whether any of its arguments are non-zero => `isSome`
        // For example: (R = sum(A B C), R ^ X) -> (R = isNone?(A B C), R ^ X)
        if (trick_sum_booly(ml, offset, indexR, countsR, sum, argCount)) return;
      }
    }

    TRACE(' - cut_sum changed nothing');
    pc += opSize;
  }

  function cut_xnor(ml, offset) {
    var argCount = ml_dec16(ml, offset + 1);
    TRACE(' ! cut_xnor;', argCount, 'args');

    if (argCount === 2) {
      var indexA = readIndex(ml, offset + OFFSET_C_A);
      var indexB = readIndex(ml, offset + OFFSET_C_B);
      var countsA = getCounts(bounty, indexA);
      var countsB = getCounts(bounty, indexB);
      TRACE(' - 2 args!', indexA, '!^', indexB, '::', domain__debug(getDomain(indexA, true)), '!^', domain__debug(getDomain(indexB, true)));
      ASSERT(!countsA || !domain_isSolved(getDomain(indexA, true)), 'if it has counts it shouldnt be solved', countsA, indexA, domain__debug(getDomain(indexA, true)));
      ASSERT(!countsB || !domain_isSolved(getDomain(indexB, true)), 'if it has counts it shouldnt be solved', countsB, indexB, domain__debug(getDomain(indexB, true)));
      TRACE('  - counts:', countsA, countsB, ', meta:', bounty__debugMeta(bounty, indexA), '!^', bounty__debugMeta(bounty, indexB));

      if (indexA === indexB) {
        TRACE(' - argcount=2 and A==B, requesting minimzer cycle');
        requestAnotherCycle = true;
        return;
      }

      if (countsA === 1) {
        return leaf_xnor(ml, offset, indexA, indexB, indexA, indexB);
      }

      if (countsB === 1) {
        return leaf_xnor(ml, offset, indexB, indexA, indexA, indexB);
      } // (do we care about constants here? technically the minimizer should eliminate xnors with constants... so, no?)


      if (countsA > 0 && countsB > 0) {
        var metaA = getMeta(bounty, indexA, true); // Keep booly flags

        var metaB = getMeta(bounty, indexB, true);
        TRACE(' - considering whether A and B are xnor pseudo aliases;', bounty__debugMeta(bounty, indexA), '!^', bounty__debugMeta(bounty, indexB));
        var boolyA = !hasFlags(metaA, BOUNTY_FLAG_NOT_BOOLY);
        var boolyB = !hasFlags(metaB, BOUNTY_FLAG_NOT_BOOLY);
        TRACE(' - ', boolyA || boolyB ? 'yes' : 'no', ' ->', boolyA, '||', boolyB);

        if (boolyA || boolyB) {
          // We declare A and alias of B. they are both used as booly only and the xnor states that if and
          // only if A is truthy then B must be truthy too. since we confirmed both are only used as booly
          // their actual non-zero values are irrelevant and the rewrite is safe. the last thing to make
          // sure is that the domains are updated afterwards and not synced and clobbered by the alias code.
          return trick_xnor_pseudoSame(ml, offset, indexA, boolyA, indexB, boolyB);
        }
      }
    }

    TRACE(' - cut_xnor did nothing');
    pc += SIZEOF_C + argCount * 2;
  }

  function cut_xor(ml, offset) {
    var indexA = readIndex(ml, offset + OFFSET_C_A);
    var indexB = readIndex(ml, offset + OFFSET_C_B);
    var countsA = getCounts(bounty, indexA);
    var countsB = getCounts(bounty, indexB);
    TRACE(' ! cut_xor; ', indexA, '^', indexB, '::', domain__debug(getDomain(indexA, true)), '^', domain__debug(getDomain(indexB, true)));
    TRACE('  - counts:', countsA, countsB, ', meta:', bounty__debugMeta(bounty, indexA), '^', bounty__debugMeta(bounty, indexB));
    ASSERT(!countsA || !domain_isSolved(getDomain(indexA, true)), 'if it has counts it shouldnt be solved', countsA, indexA, domain__debug(getDomain(indexA, true)));
    ASSERT(!countsB || !domain_isSolved(getDomain(indexB, true)), 'if it has counts it shouldnt be solved', countsB, indexB, domain__debug(getDomain(indexB, true)));
    ASSERT(ml_dec16(ml, offset + 1) === 2, 'xor always has 2 args');

    if (indexA === indexB) {
      TRACE(' - argcount=2 and A==B, requesting minimzer cycle');
      requestAnotherCycle = true;
      return;
    }

    if (countsA === 1) {
      return leaf_xor(ml, offset, indexA, indexB, indexA, indexB);
    }

    if (countsB === 1) {
      return leaf_xor(ml, offset, indexB, indexA, indexA, indexB);
    }

    var A = getDomain(indexA, true);
    var B = getDomain(indexB, true);

    if (!domain_isBooly(A) || !domain_isBooly(B)) {
      TRACE(' / at least A or B is already booly solved. bailing so minimizer can take over.');
      requestAnotherCycle = true;
      return;
    }

    if (countsA > 0 && countsB > 0) {
      var metaA = getMeta(bounty, indexA, true); // Keep booly flags

      var metaB = getMeta(bounty, indexB, true);
      var AonlyUsedBooly = !hasFlags(metaA, BOUNTY_FLAG_NOT_BOOLY);
      var BonlyUsedBooly = !hasFlags(metaB, BOUNTY_FLAG_NOT_BOOLY); // Meta should only be these flags

      var TRICK_INV_XOR_FLAGS = BOUNTY_FLAG_SOME | BOUNTY_FLAG_NALL | BOUNTY_FLAG_IMP_LHS | BOUNTY_FLAG_IMP_RHS | BOUNTY_FLAG_XOR;

      if (countsA < BOUNTY_MAX_OFFSETS_TO_TRACK) {
        // Check for some/nall/imp/xor. if A only concerns these then we can invert those
        // ops and remove the xor. Note: LTE only works when it could be an implication,
        // so we can omit a check for that as those LTE's should morph into IMP eventually
        TRACE('  - A; only contains good flags?', (metaA & TRICK_INV_XOR_FLAGS) === metaA);

        if ((metaA & TRICK_INV_XOR_FLAGS) === metaA) {
          if (trick_xor_elimination(offset, indexA, countsA, indexB)) return;
        }

        if (countsA === 2) {
          if (hasFlags(metaA, BOUNTY_FLAG_ISALL_RESULT)) {
            // R^A, R=all?(X Y Z)  ->   A=nall(X Y Z)
            if (trick_isall_xor(indexA, indexB, offset, countsA, countsB)) return;
          }

          if (AonlyUsedBooly && hasFlags(metaA, BOUNTY_FLAG_ISSOME_RESULT)) {
            // R^X, R=some?(A B C)   ->    X=none?(A B C)
            if (trick_issome_xor(indexA, indexB, offset, countsA, countsB)) return;
          }

          if (metaA === (BOUNTY_FLAG_XOR | BOUNTY_FLAG_SOME)) {
            if (trick_some_xor(indexA, indexB, offset, countsA)) return;
          }
        }

        var sB = domain_size(B);
        if (trick_xor_alias(indexA, indexB, countsA, B, sB, BonlyUsedBooly)) return;
      }

      if (countsB < BOUNTY_MAX_OFFSETS_TO_TRACK) {
        // Check for some/nall/imp/xor. if B only concerns these then we can invert those
        // ops and remove the xor. Note: LTE only works when it could be an implication,
        // so we can omit a check for that as those LTE's should morph into IMP eventually
        TRACE('  - B; only contains good flags?', (metaB & TRICK_INV_XOR_FLAGS) === metaB);

        if (domain_isBoolyPair(B) && (metaB & TRICK_INV_XOR_FLAGS) === metaB) {
          if (trick_xor_elimination(offset, indexB, countsB, indexA)) return;
        }

        if (countsB === 2) {
          if (hasFlags(metaB, BOUNTY_FLAG_ISALL_RESULT)) {
            // R^B, R=all?(X Y Z)  ->   B=nall(X Y Z)
            if (trick_isall_xor(indexB, indexA, offset, countsB, countsA)) return;
          }

          if (BonlyUsedBooly && hasFlags(metaB, BOUNTY_FLAG_ISSOME_RESULT)) {
            // R^X, R=some?(A B C)   ->    X=none?(A B C)
            if (trick_issome_xor(indexB, indexA, offset, countsB, countsA)) return;
          }

          if (metaB === (BOUNTY_FLAG_XOR | BOUNTY_FLAG_SOME)) {
            if (trick_some_xor(indexB, indexA, offset, countsB)) return;
          }
        }

        var sA = domain_size(A);
        if (trick_xor_alias(indexB, indexA, countsB, A, sA, AonlyUsedBooly)) return;
      }
    }

    TRACE(' / cut_xor changed nothing');
    pc += SIZEOF_C_2;
  } // ##############


  function leaf_diff_pair(ml, offset, leafIndex, otherIndex, indexA, indexB) {
    TRACE('   - leaf_diff_pair;', leafIndex, 'is a leaf var, A != B,', indexA, '!=', indexB);
    solveStack.push(function (_, force, getDomain, setDomain) {
      TRACE(' - leaf_diff_pair; solving', indexA, '!=', indexB, '  ->  ', domain__debug(getDomain(indexA)), '!=', domain__debug(getDomain(indexB)));
      var A = getDomain(indexA);
      var B = getDomain(indexB);

      if (domain_size(A) < domain_size(B)) {
        var v = force(indexA);
        setDomain(indexB, domain_removeValue(B, v));
      } else {
        var _v = force(indexB);

        setDomain(indexA, domain_removeValue(A, _v));
      }

      ASSERT(getDomain(indexA) !== getDomain(indexB), 'D ought to have at least a value other dan v');
    });
    ml_eliminate(ml, offset, SIZEOF_C_2);
    bounty_markVar(bounty, leafIndex);
    bounty_markVar(bounty, otherIndex);
    somethingChanged();
  }

  function leaf_imp(ml, offset, indexA, indexB, leafIsA) {
    TRACE('   - leaf_imp;', leafIsA ? 'A' : 'B', 'is a leaf var, A -> B;', indexA, '->', indexB);
    ASSERT(typeof indexA === 'number', 'index A should be number', indexA);
    ASSERT(typeof indexB === 'number', 'index B should be number', indexB);
    solveStack.push(function (_, force, getDomain, setDomain) {
      TRACE(' - leaf_imp; solving', indexA, '->', indexB, '  =>  ', domain__debug(getDomain(indexA)), '->', domain__debug(getDomain(indexB)), '  =>  ', domain_max(getDomain(indexA)), '->', domain_min(getDomain(indexB)));
      var A = getDomain(indexA);
      var B = getDomain(indexB); // TODO: weigh in value dists here

      if (leafIsA) {
        TRACE(' - A was leaf; A=', domain__debug(A), '->', domain__debug(B)); // (we could simply and safely set A to 0 here and skip the solvestack part completely)

        if (domain_hasNoZero(B)) {
          var nA = domain_removeValue(A, 0);
          ASSERT(nA, 'A should not be empty');
          if (A !== nA) setDomain(indexA, nA);
        } else {
          var _nA = domain_intersectionValue(A, 0);

          ASSERT(_nA, 'A should not be empty');
          if (A !== _nA) setDomain(indexA, _nA);
        }
      } else {
        TRACE(' - B was leaf; A=', domain__debug(A), '->', domain__debug(B)); // (we could simply and safely set B to nonzero here and skip the solvestack part completely)

        if (domain_hasNoZero(A)) {
          var nB = domain_removeValue(B, 0);
          ASSERT(nB, 'B should not be empty');
          if (A !== nB) setDomain(indexB, nB);
        } else {
          var _nB = domain_intersectionValue(B, 0);

          ASSERT(_nB, 'B should not be empty');
          if (B !== _nB) setDomain(indexB, _nB);
        }
      }
    });
    ml_eliminate(ml, offset, SIZEOF_C_2);
    bounty_markVar(bounty, indexA);
    bounty_markVar(bounty, indexB);
    somethingChanged();
  }

  function leaf_isdiff(ml, offset, indexA, indexB, indexR, indexL) {
    TRACE('   - leaf_isdiff; index', indexL, 'is a leaf var, R = A !=? B,', indexR, '=', indexA, '!=?', indexB, '  ->  ', domain__debug(getDomain(indexR)), '=', domain__debug(getDomain(indexA)), '!=?', domain__debug(getDomain(indexB)));
    ASSERT(ml_dec16(ml, offset + 1) === 2);
    solveStack.push(function (_, force, getDomain, setDomain) {
      TRACE(' - leaf_isdiff');
      var A = getDomain(indexA);
      var B = getDomain(indexB);
      var R = getDomain(indexR);
      TRACE(' - leaf=', indexL, ';', indexR, '=', indexA, '!=?', indexB, '  =>  ', domain__debug(R), '=', domain__debug(A), '!=?', domain__debug(B), ', AB=', domain__debug(domain_intersection(A, B)));

      if (domain_isSolved(A)) {
        if (domain_isSolved(B)) {
          TRACE(' - A and B are solved, set R to reflect', domain_getValue(A), '!=', domain_getValue(B));
          if (A !== B) R = domain_removeValue(R, 0);else R = domain_removeGtUnsafe(R, 0);
          setDomain(indexR, R);
        } else if (domain_isBooly(R)) {
          TRACE(' - A is solved but B and R arent, remove A from B and set R>0');
          B = domain_removeValue(B, domain_getValue(A));
          setDomain(indexB, B);
          R = domain_removeValue(R, 0);
          setDomain(indexR, R);
        } else {
          TRACE(' - A and R are solved, set B to reflect it');

          if (domain_isZero(R)) {
            TRACE(' - R=0 so A==B');
            setDomain(indexB, A);
          } else {
            TRACE(' - R>0 so A!=B');
            B = domain_removeValue(B, domain_getValue(A));
            setDomain(indexB, B);
          }
        }
      } else if (domain_isSolved(B)) {
        if (domain_isBooly(R)) {
          TRACE(' - B is solved but A and R are not. Remove B from A and set R>0');
          A = domain_removeValue(A, domain_getValue(B));
          setDomain(indexA, A);
          R = domain_removeValue(R, 0);
          setDomain(indexR, R);
        } else {
          TRACE(' - B and R are solved but A is not. Update A to reflect R');

          if (domain_isZero(R)) {
            TRACE(' - R=0 so A==B');
            setDomain(indexA, B);
          } else {
            TRACE(' - R>0 so A!=B');
            A = domain_removeValue(A, domain_getValue(B));
            setDomain(indexA, A);
          }
        }
      } else if (domain_isBooly(R)) {
        TRACE(' - A, B, and R arent solved. force A and remove it from B (if A and B intersect) and set R>0');

        if (domain_intersection(A, B) !== EMPTY) {
          B = domain_removeValue(B, force(indexA));
          setDomain(indexB, B);
        }

        R = domain_removeValue(R, 0);
        setDomain(indexR, R);
      } else {
        TRACE(' - A and B arent solved but R is. update A and B to reflect R');

        if (domain_isZero(R)) {
          TRACE(' - R=0 so A==B');
          var vA = force(indexA, domain_intersection(A, B));
          ASSERT(domain_intersection(B, domain_createValue(vA)) !== EMPTY);
          B = domain_createValue(vA);
          setDomain(indexB, B);
        } else {
          var _vA = force(indexA);

          B = domain_removeValue(B, _vA);
          setDomain(indexB, B);
        }
      }

      TRACE(' - afterwards: R:' + indexR + ':' + domain__debug(getDomain(indexR)), ' = A:' + indexA + ':' + domain__debug(getDomain(indexA)), ' !=? B:' + indexB + ':' + domain__debug(getDomain(indexB)), ', AB=', domain__debug(domain_intersection(getDomain(indexA), getDomain(indexB)))); // 3 things must hold;
      // - A or B must be solved or not intersect (otherwise future reductions may violate R)
      // - R must not be booly (obviously)
      // - R's state must reflect whether or not A shares a value with B (which by the above should at most be one value, but that's not helpful)

      ASSERT(getDomain(indexA));
      ASSERT(getDomain(indexB));
      ASSERT(getDomain(indexR));
      ASSERT(domain_intersection(getDomain(indexA), getDomain(indexB)) === EMPTY || domain_isSolved(getDomain(indexA)) || domain_isSolved(getDomain(indexB)), 'at least A or B must be solved in order to ensure R always holds');
      ASSERT(!domain_isBooly(getDomain(indexR)), 'R must not be a booly to ensure the constraint always holds');
      ASSERT(domain_intersection(getDomain(indexA), getDomain(indexB)) === EMPTY === domain_hasNoZero(getDomain(indexR)), 'R must be nonzero if A and B share no elements');
    });
    ASSERT(ml_dec16(ml, offset + 1) === 2, 'argcount should be 2 at the moment');
    ml_eliminate(ml, offset, SIZEOF_CR_2);
    bounty_markVar(bounty, indexA);
    bounty_markVar(bounty, indexB);
    bounty_markVar(bounty, indexR);
    somethingChanged();
  }

  function leaf_isall(ml, offset, argCount, indexR) {
    TRACE('   - leaf_isall;', indexR, 'is a leaf var, R = all?(', argCount, 'x ),', indexR, '= all?(...)');
    var args = markAndCollectArgs(ml, offset, argCount);
    solveStack.push(function (_, force, getDomain, setDomain) {
      TRACE(' - leaf_isall; ', indexR, '= isAll(', args.join(' '), ')  ->  ', domain__debug(getDomain(indexR)), ' = isAll(', args.map(function (index) {
        return domain__debug(getDomain(index));
      }).join(' '), ')');
      var vR = 1;

      for (var i = 0; i < argCount; ++i) {
        if (force(args[i]) === 0) {
          vR = 0;
          break;
        }
      }

      var oR = getDomain(indexR);
      var R = domain_resolveAsBooly(oR, vR);
      ASSERT(R, 'R should be able to at least represent the solution');
      setDomain(indexR, R);
    });
    ml_eliminate(ml, offset, SIZEOF_C + argCount * 2 + 2);
    bounty_markVar(bounty, indexR);
    somethingChanged();
  }

  function leaf_isall_arg_result(ml, indexR, countsR) {
    // R is only result or arg of isall ops.
    // for trick R must be result _and_ arg in _all_ the isalls
    // if R is only part of `R = all?(R ...)` ops then leaf(R) and eliminate the constraint
    // if R is part of `R = all?(R ...)` and `S = all?(R ...)` then leaf R and morph to imps S->A, S->B all other args
    var R = getDomain(indexR, true);

    if (!domain_isBool(R)) {
      TRACE(' - R is not bool, bailing');
      return false;
    } // First verify, scan, and collect


    var argOnlyOffsets = [];
    var resultOnlyOffsets = [];
    var argAndResultOffsets = [];
    var allArgs = [];
    var offsets = [];

    for (var i = 0; i < countsR; ++i) {
      var offset = bounty_getOffset(bounty, indexR, i);
      TRACE('    - i=', i, ', offset=', offset);
      ASSERT(ml_dec8(ml, offset) === ML_ISALL); // Each offset could be visited twice if this trick is applied

      if (offsets.indexOf(offset) < 0) {
        var argCount = ml_dec16(ml, offset + 1);
        var resultIndex = readIndex(ml, offset + SIZEOF_C + argCount * 2);
        var args = [];
        var foundAsArg = false;

        for (var j = 0; j < argCount; ++j) {
          var index = readIndex(ml, offset + SIZEOF_C + j * 2);
          args.push(index);
          if (index === indexR) foundAsArg = true;
        }

        TRACE('    - is result?', resultIndex === indexR, ', is arg?', foundAsArg);
        ASSERT(foundAsArg || resultIndex === indexR, 'R should be part of the isall as per bounty');
        if (resultIndex !== indexR) argOnlyOffsets.push(offset);else if (!foundAsArg) resultOnlyOffsets.push(offset);else argAndResultOffsets.push(offset);
        allArgs.push(args);
        offsets.push(offset);
      }
    }

    TRACE(' - collected: result only:', resultOnlyOffsets, ', arg only:', argOnlyOffsets, ', both result and arg:', argAndResultOffsets); // Three cases: either R was a result-only or arg-only in at least one isall, or not. yes, three cases.

    if (resultOnlyOffsets.length) {
      TRACE(' - there was at least one isall where R was the result only. cant apply this trick. bailing');
      return false;
    }

    ASSERT(argAndResultOffsets.length, 'bounty found R to be result and arg of isall and there were no isalls where R was result only so there must be at least one isall with R being result and arg'); // Two cases left: either R was result AND arg in all isalls or there was at least one isall where it was arg only

    if (argOnlyOffsets.length) {
      return _leafIsallArgResultMaybe(ml, indexR, allArgs, offsets, R, countsR, argOnlyOffsets, argAndResultOffsets);
    }

    return _leafIsallArgResultOnly(ml, indexR, allArgs, offsets, R);
  }

  function _leafIsallArgResultMaybe(ml, indexR, allArgs, offsets, R, countsR, argOnlyOffsets, argAndResultOffsets) {
    TRACE(' - confirmed, R is only part of isall where R is result and arg or just arg and at least one of each');
    TRACE(' - R = all?(R ...), S = all?(R ...)    =>    S -> A, S -> B, ... for all args of the isalls'); // Note: one isall contributes 2 counts, the other only 1

    if (countsR !== 3) {
      TRACE(' - countsR != 3, for now we bail on this. maybe in the future we can do this.');
      return false;
    }

    ASSERT(argOnlyOffsets.length === 1 && argAndResultOffsets.length === 1, 'for now');
    var argOnlyIsallOffset = argOnlyOffsets[0];
    var argOnlyIsallArgCount = ml_dec16(ml, argOnlyIsallOffset + 1);
    var argAndResultIsallOffset = argAndResultOffsets[0];
    var argAndResultIsallArgCount = ml_dec16(ml, argAndResultIsallOffset + 1);
    var indexS = readIndex(ml, argOnlyIsallOffset + SIZEOF_C + argOnlyIsallArgCount * 2);

    if (argOnlyIsallArgCount !== 2 || argAndResultIsallArgCount !== 2) {
      var ok = _leafIsallArgResultExcess(ml, indexR, indexS, allArgs);

      if (!ok) return false;
    }

    var indexA = readIndex(ml, argOnlyIsallOffset + OFFSET_C_A);
    if (indexA === indexR) indexA = readIndex(ml, argOnlyIsallOffset + OFFSET_C_B);
    var indexB = readIndex(ml, argAndResultIsallOffset + OFFSET_C_A);
    if (indexB === indexR) indexB = readIndex(ml, argAndResultIsallOffset + OFFSET_C_B);
    TRACE_MORPH('R = all?(R A), S = all?(R B)', 'S -> A, S -> B', 'when R is leaf');
    TRACE(' - indexes;', indexR, '= all?(', indexR, indexA, '),', indexS, '= all?(', indexR, indexB, ')');
    TRACE(' - domains;', domain__debug(getDomain(indexR)), '= all?(', domain__debug(getDomain(indexR)), domain__debug(getDomain(indexA)), '),', domain__debug(getDomain(indexS)), '= all?(', domain__debug(getDomain(indexR)), indexB, ')');
    ml_cr2c2(ml, argOnlyIsallOffset, argOnlyIsallOffset, ML_IMP, indexS, indexA);
    ml_cr2c2(ml, argAndResultIsallOffset, argAndResultIsallOffset, ML_IMP, indexS, indexB);
    solveStack.push(function (_, force, getDomain, setDomain) {
      TRACE('_leafIsallArgResultMaybe');
      var R = getDomain(indexR);
      var nR = R; // R = R &? A

      if (force(indexA) === 0) {
        TRACE(' - A is 0 so R cant be 1');
        nR = domain_removeGtUnsafe(nR, 0);
      } else {
        // S = R &? B
        var vS = force(indexS);

        if (vS) {
          TRACE(' - S>0 so R must be nonzero');
          nR = domain_removeValue(nR, 0);
        } else {
          ASSERT(vS === 0);

          if (force(indexB) > 0) {
            TRACE(' - S=0 and B>0 so R must be zero');
            nR = domain_removeGtUnsafe(nR, 0);
          }
        }
      }

      TRACE(' - final R:', domain__debug(nR));
      ASSERT(nR);
      if (R !== nR) setDomain(indexR, nR);
    });
    bounty_markVar(bounty, indexA);
    bounty_markVar(bounty, indexB);
    bounty_markVar(bounty, indexR);
    bounty_markVar(bounty, indexS);
    somethingChanged();
    return true;
  }

  function _leafIsallArgResultExcess(ml, indexR, indexS, argsPerIsall) {
    TRACE(' - _leafIsallArgResultExcess');
    TRACE(' - collecting excess args now; indexR:', indexR, ', all args:', argsPerIsall); // Collect all args except indexR and the first arg of the first two isalls, or second if first is indexR
    // we need to recycle spaces for that

    var toCompile = [];

    for (var i = 0; i < argsPerIsall.length; ++i) {
      var args = argsPerIsall[i];
      TRACE('   -', i, '; isall args:', args);
      var gotOne = i >= 2;

      for (var j = 0; j < args.length; ++j) {
        var index = args[j];
        TRACE('     -', j, '; index:', index, index === indexR);

        if (index !== indexR) {
          if (!gotOne && j < 2) {
            TRACE('       - skipped (compiled by caller)'); // Skip the first non-R for the first two isalls

            gotOne = true;
          } else {
            TRACE('       - collected');
            toCompile.push(index);
          }
        }
      }
    }

    TRACE(' - excess args to compile in recycled spaces:', toCompile); // There could potentially be no args to compile here. and that's okay.

    var count = toCompile.length;

    if (count) {
      TRACE(' - found', count, 'extra args to compile:', toCompile); // Start by collecting count recycled spaces

      var bins = ml_getRecycleOffsets(ml, 0, count, SIZEOF_C_2);

      if (!bins) {
        TRACE(' - Was unable to find enough free space to fit', count, 'IMPs, bailing');
        return false;
      }

      var _i = 0;

      while (_i < count) {
        var currentOffset = bins.pop();
        ASSERT(ml_dec8(ml, currentOffset) === ML_JMP, 'should only get jumps here'); // Might trap a case where we clobber

        var size = ml_getOpSizeSlow(ml, currentOffset);
        ASSERT(size >= SIZEOF_C_2, 'this is what we asked for');

        do {
          var _index = toCompile[_i];
          TRACE('  - compiling lte:', indexS, '->', _index, '   =>    ', domain__debug(getDomain(indexS, true)), '->', domain__debug(getDomain(_index, true)));
          ml_any2c(ml, currentOffset, ml_getOpSizeSlow(ml, currentOffset), ML_IMP, [indexS, _index]);
          ++_i;
          size -= SIZEOF_C_2;
          currentOffset += SIZEOF_C_2;
        } while (size >= SIZEOF_C_2 && _i < count);

        if (process.env.NODE_ENV !== 'production') {
          ml_validateSkeleton(ml); // Cant check earlier
        }
      }

      TRACE(' - finished compiling extra args');
    }

    return true;
  }

  function _leafIsallArgResultOnly(ml, indexR, allArgs, offsets, R) {
    TRACE(' - confirmed, all isalls have R as result _and_ arg; args:', allArgs, ', offsets:', offsets);
    TRACE(' - R is a leaf and we eliminate all isalls associated to R');
    solveStack.push(function (_, force, getDomain, setDomain) {
      TRACE(' - leaf_isall_arg_result');
      ASSERT(domain_isBool(R), 'R was a bool (asserted above, and as leaf, that should not have changed)');
      ASSERT(domain_isBool(getDomain(indexR))); // If all args besides R are set, then R can be anything. otherwise R is 0.
      // need to check this for all isalls. if any one causes R to be 0 then that's that.

      var allSet = true;

      for (var i = 0, len = allArgs.length; i < len; ++i) {
        var args = allArgs[i];

        for (var j = 0, len2 = args.length; j < len2; ++j) {
          var index = args[j];

          if (index !== indexR) {
            var D = getDomain(index);

            if (!domain_hasNoZero(D)) {
              allSet = false; // Either it's zero or booly, either way set R to 0 and be done.
            }
          }
        }

        if (!allSet) {
          TRACE(' - foundAsArg an isall where not all other args were set so forcing R to 0'); // Remember: R is a bool, asserted above. twice now. so this cant possibly fail. (watch it fail. sorry, future me!)

          setDomain(indexR, domain_createValue(0));
          break;
        }
      } // Otherwise R kind of determines itself so no choice is made :)


      TRACE(' - was R forced to 0?', !allSet);
    });
    TRACE(' - now marking vars and eliminating isall constraints');

    for (var i = 0, len = offsets.length; i < len; ++i) {
      var offset = offsets[i];
      var args = allArgs[i];
      TRACE('    - i=', i, ', offset=', offset, ', args=', args);
      TRACE_MORPH('R = all?(R ...)', '', 'if R only touches isalls on result _and_ arg then R is still a leaf');
      ASSERT(args.length === ml_dec16(ml, offset + 1), 'should be able to use this shortcut (not sure whether its actually faster tho)');
      ml_eliminate(ml, offset, SIZEOF_C + args.length * 2 + 2);

      for (var j = 0, len2 = args.length; j < len2; ++j) {
        TRACE('      - marking', args[j]);
        bounty_markVar(bounty, args[j]);
      }
    }

    somethingChanged();
    return true;
  }

  function leaf_islt(ml, offset, indexA, indexB, indexR, indexL) {
    TRACE('   - leaf_islt;', indexL, 'is a leaf var, R = A <? B,', indexR, '=', indexA, '<?', indexB, '  ->  ', domain__debug(getDomain(indexR)), '=', domain__debug(getDomain(indexA)), '<?', domain__debug(getDomain(indexB)));
    solveStack.push(function (_, force, getDomain, setDomain) {
      TRACE(' - leaf_islt');
      TRACE(' - leaf index=', indexL, ';', indexR, '=', indexA, '<?', indexB, '  ->  ', domain__debug(getDomain(indexR)), '=', domain__debug(getDomain(indexA)), '<?', domain__debug(getDomain(indexB)));
      var A = getDomain(indexA);
      var B = getDomain(indexB);
      var R = getDomain(indexR); // R doesnt need to be booly...

      if (domain_isBooly(R)) {
        TRACE(' - R is booly, just force A and B and reflect the result in R');
        var vA = force(indexA);
        var vB = force(indexB);
        if (vA < vB) R = domain_removeValue(R, 0);else R = domain_removeGtUnsafe(R, 0);
        setDomain(indexR, R);
      } else if (domain_isZero(R)) {
        TRACE(' - R=0 so force A>=B by setting A=maxA() and B=min(B)'); // There are complexities with edge cases so for now just take the easy road;
        // assuming the problem was always solveable before; max(A) >= min(B)

        A = domain_createValue(domain_max(A));
        B = domain_createValue(domain_min(B));
        TRACE('   - now ==>', domain__debug(A), '>=', domain__debug(B));
        setDomain(indexA, A);
        setDomain(indexB, B);
      } else {
        ASSERT(domain_hasNoZero(R));
        TRACE(' - R>0 so force A<B ==>', domain__debug(A), '<', domain__debug(B)); // There are complexities with edge cases so for now just take the easy road;
        // assuming the problem was always solveable before; min(A) < max(B)

        A = domain_createValue(domain_min(A));
        B = domain_createValue(domain_max(B));
        TRACE('   - now ==>', domain__debug(A), '>=', domain__debug(B));
        setDomain(indexA, A);
        setDomain(indexB, B);
      }

      TRACE(' - R:', domain__debug(getDomain(indexR)), '= A:', domain__debug(getDomain(indexA)), '< B:', domain__debug(getDomain(indexB)));
      ASSERT(getDomain(indexA));
      ASSERT(getDomain(indexB));
      ASSERT(getDomain(indexR));
      ASSERT(!domain_isBooly(getDomain(indexR)));
      ASSERT(!domain_isZero(getDomain(indexR)) === domain_max(getDomain(indexA)) < domain_min(getDomain(indexB)), 'should hold constraint');
    });
    ml_eliminate(ml, offset, SIZEOF_VVV);
    bounty_markVar(bounty, indexA);
    bounty_markVar(bounty, indexB);
    bounty_markVar(bounty, indexR);
    somethingChanged();
  }

  function leaf_islte(ml, offset, indexA, indexB, indexR, indexL) {
    TRACE('   - leaf_islte;', indexL, 'is a leaf var, R = A <=? B,', indexR, '=', indexA, '<=?', indexB, '  ->  ', domain__debug(getDomain(indexR)), '=', domain__debug(getDomain(indexA)), '<=?', domain__debug(getDomain(indexB)));
    solveStack.push(function (_, force, getDomain, setDomain) {
      TRACE(' - leaf_islte');
      TRACE(' - leaf index=', indexL, ';', indexR, '=', indexA, '<=?', indexB, '  ->  ', domain__debug(getDomain(indexR)), '=', domain__debug(getDomain(indexA)), '<=?', domain__debug(getDomain(indexB)));
      var A = getDomain(indexA);
      var B = getDomain(indexB);
      var R = getDomain(indexR); // R doesnt need to be booly...

      if (domain_isBooly(R)) {
        TRACE(' - R is booly, just force A and B and reflect the result in R');
        var vA = force(indexA);
        var vB = force(indexB);
        if (vA <= vB) R = domain_removeValue(R, 0);else R = domain_removeGtUnsafe(R, 0);
        setDomain(indexR, R);
      } else if (domain_isZero(R)) {
        TRACE(' - R=0 so force A>=B by setting A=maxA() and B=min(B)'); // There are complexities with edge cases so for now just take the easy road;
        // assuming the problem was always solveable before; max(A) > min(B)

        A = domain_createValue(domain_max(A));
        B = domain_createValue(domain_min(B));
        TRACE('   - now ==>', domain__debug(A), '>', domain__debug(B));
        setDomain(indexA, A);
        setDomain(indexB, B);
      } else {
        ASSERT(domain_hasNoZero(R));
        TRACE(' - R>0 so force A<=B ==>', domain__debug(A), '<=', domain__debug(B)); // There are complexities with edge cases so for now just take the easy road;
        // assuming the problem was always solveable before; min(A) <= max(B)

        A = domain_createValue(domain_min(A));
        B = domain_createValue(domain_max(B));
        TRACE('   - now ==>', domain__debug(A), '<=', domain__debug(B));
        setDomain(indexA, A);
        setDomain(indexB, B);
      }

      TRACE(' - R:', domain__debug(getDomain(indexR)), '= A:', domain__debug(getDomain(indexA)), '<= B:', domain__debug(getDomain(indexB)));
      ASSERT(getDomain(indexA));
      ASSERT(getDomain(indexB));
      ASSERT(getDomain(indexR));
      ASSERT(!domain_isBooly(getDomain(indexR)));
      ASSERT(!domain_isZero(getDomain(indexR)) === domain_max(getDomain(indexA)) <= domain_min(getDomain(indexB)), 'should hold constraint');
    });
    ml_eliminate(ml, offset, SIZEOF_VVV);
    bounty_markVar(bounty, indexA);
    bounty_markVar(bounty, indexB);
    bounty_markVar(bounty, indexR);
    somethingChanged();
  }

  function leaf_isnall(ml, offset, argCount, indexR, counts) {
    TRACE('   - leaf_isnall;', indexR, 'is a leaf var with counts:', counts, ', R = nall?(', argCount, 'x ),', indexR, '= all?(...)');
    var args = markAndCollectArgs(ml, offset, argCount);
    solveStack.push(function (_, force, getDomain, setDomain) {
      TRACE(' - leaf_isnall');
      TRACE('-', indexR, '= nall?(', args, ')  ->  ', domain__debug(getDomain(indexR)), ' = nall?(', args.map(function (index) {
        return domain__debug(getDomain(index));
      }), ')');
      var vR = 0;

      for (var i = 0; i < argCount; ++i) {
        if (force(args[i]) === 0) {
          TRACE(' - found at least one arg that is zero so R>0');
          vR = 1;
          break;
        }
      }

      var oR = getDomain(indexR);
      var R = domain_resolveAsBooly(oR, vR);
      setDomain(indexR, R);
      ASSERT(getDomain(indexR));
      ASSERT(domain_hasNoZero(getDomain(indexR)) === args.some(function (index) {
        return domain_isZero(getDomain(index));
      }));
    });
    ml_eliminate(ml, offset, SIZEOF_C + argCount * 2 + 2);
    bounty_markVar(bounty, indexR);
    somethingChanged();
  }

  function leaf_issame(ml, offset, indexA, indexB, indexR, indexL) {
    TRACE('   - leaf_issame; index', indexL, 'is a leaf var, R = A ==? B,', indexR, '=', indexA, '==?', indexB, '  ->  ', domain__debug(getDomain(indexR)), '=', domain__debug(getDomain(indexA)), '==?', domain__debug(getDomain(indexB)));
    ASSERT(ml_dec16(ml, offset + 1) === 2, 'for now argcount should be 2');
    solveStack.push(function (_, force, getDomain, setDomain) {
      TRACE(' - leaf_issame; leaf=', indexL, ';', indexR, '=', indexA, '==?', indexB, '  ->  ', domain__debug(getDomain(indexR)), '=', domain__debug(getDomain(indexA)), '==?', domain__debug(getDomain(indexB)));
      var A = getDomain(indexA);
      var B = getDomain(indexB);
      var AB = domain_intersection(A, B);
      var R = getDomain(indexR);
      TRACE(' - A:', domain__debug(A), ', B:', domain__debug(B), ', AB:', domain__debug(AB), ', solved?', domain_isSolved(A), domain_isSolved(B));

      if (!domain_isSolved(R)) {
        if (!AB) {
          TRACE('   - A&B is empty so R=0');
          R = domain_resolveAsBooly(R, false);
        } else if (domain_isSolved(A)) {
          TRACE('   - A is solved so R=A==B', A === B);
          R = domain_resolveAsBooly(R, A === B);
        } else if (domain_isSolved(B)) {
          TRACE('   - B is solved and A wasnt. A&B wasnt empty so we can set A=B');
          setDomain(indexA, B);
          R = domain_resolveAsBooly(R, true);
        } else {
          TRACE('   - some values overlap between A and B and neither is solved.. force all');
          var v = domain_min(AB);
          var V = domain_createValue(v);
          setDomain(indexA, V);
          setDomain(indexB, V);
          R = domain_resolveAsBooly(R, true);
        }

        TRACE(' - R is now', domain__debug(R));
        ASSERT(R, 'leaf should at least have the resulting value');
        setDomain(indexR, R);
      } else if (domain_isZero(R)) {
        TRACE(' - R=0 so make sure AB is empty');

        if (AB) {
          TRACE(' - it wasnt, making it so now');
          if (domain_isSolved(A)) setDomain(indexB, domain_removeValue(B, domain_getValue(A)));else setDomain(indexA, domain_removeValue(A, force(indexB)));
        }
      } else {
        force(indexA, AB);
        force(indexB, getDomain(indexA));
      }

      ASSERT(getDomain(indexR));
      ASSERT(getDomain(indexA));
      ASSERT(getDomain(indexB));
      ASSERT(!domain_isBooly(getDomain(indexR)));
      ASSERT(domain_isSolved(getDomain(indexA)) || domain_isSolved(getDomain(indexB)) || !domain_intersection(getDomain(indexA), getDomain(indexB)), 'either A or B is solved OR they have no intersecting values');
      ASSERT(Boolean(domain_intersection(getDomain(indexA), getDomain(indexB))) === !domain_isZero(getDomain(indexR)));
      ASSERT(!domain_isZero(getDomain(indexR)) ? domain_isSolved(getDomain(indexA)) && domain_isSolved(getDomain(indexB)) : true, 'if R>0 then A and B must be solved');
    });
    ml_eliminate(ml, offset, SIZEOF_CR_2);
    bounty_markVar(bounty, indexA);
    bounty_markVar(bounty, indexB);
    bounty_markVar(bounty, indexR);
    somethingChanged();
  }

  function leaf_issome(ml, offset, indexR, argCount) {
    TRACE('   - leaf_issome; index', indexR, 'is a leaf var, R = some?(A B ...), index=', indexR, ', R=', domain__debug(getDomain(indexR)));
    TRACE_MORPH('R = some(...)', '');
    var args = markAndCollectArgs(ml, offset, argCount);
    solveStack.push(function (_, force, getDomain, setDomain) {
      TRACE(' - leaf_issome');
      var has = false;

      for (var i = 0; i < args.length; ++i) {
        var index = args[i];

        if (force(index) > 0) {
          has = true;
          break;
        }
      }

      var R = getDomain(indexR);
      if (has) R = domain_removeValue(R, 0);else R = domain_removeGtUnsafe(R, 0);
      ASSERT(R, 'leaf should at least have the resulting value');
      setDomain(indexR, R);
    });
    ml_eliminate(ml, offset, SIZEOF_C + argCount * 2 + 2);
    bounty_markVar(bounty, indexR);
    somethingChanged();
  }

  function leaf_lt(ml, offset, indexA, indexB, leafSide) {
    TRACE('   - leaf_lt;', leafSide, 'is a leaf var, A < B,', indexA, '<', indexB);
    ASSERT(typeof indexA === 'number', 'index A should be number', indexA);
    ASSERT(typeof indexB === 'number', 'index B should be number', indexB);
    solveStack.push(function (_, force, getDomain, setDomain) {
      TRACE(' - leaf_lt; solving', indexA, '<', indexB, '  ->  ', domain__debug(getDomain(indexA)), '<', domain__debug(getDomain(indexB)));
      var A = getDomain(indexA);
      var B = getDomain(indexB);
      var maxA = domain_max(A);
      var minB = domain_min(B); // Numdom([28,29]) < numdom([15,30])

      TRACE(' - maxA >=? minB;', maxA, '>=', minB);

      if (maxA < minB) {
        TRACE(' - lt already fulfilled, no change required');
      } else if (domain_min(A) >= minB) {
        var vA = domain_min(A);
        TRACE(' - min(A) still larger than min(B) so setting A to min(A)=', vA, ' and removing all LTE from B');
        TRACE(' - so;', domain__debug(A), '=>', domain__debug(domain_removeGtUnsafe(A, vA)), 'and', domain__debug(B), '=>', domain__debug(domain_removeLte(B, vA)));
        setDomain(indexA, domain_removeGtUnsafe(A, vA));
        setDomain(indexB, domain_removeLte(B, vA));
      } else {
        TRACE(' - removing >=min(B) from A');
        setDomain(indexA, domain_removeGte(A, minB));
      }

      TRACE(' - result:', domain__debug(getDomain(indexA)), '<=', domain__debug(getDomain(indexB)));
      ASSERT(getDomain(indexA));
      ASSERT(getDomain(indexB));
      ASSERT(domain_max(getDomain(indexA)) < domain_min(getDomain(indexB)));
    });
    ml_eliminate(ml, offset, SIZEOF_C_2);
    bounty_markVar(bounty, indexA);
    bounty_markVar(bounty, indexB);
    somethingChanged();
  }

  function leaf_lte(ml, offset, indexA, indexB, leafIsA) {
    TRACE('   - leaf_lte;', leafIsA ? 'A' : 'B', 'is a leaf var, A <= B,', indexA, '<=', indexB);
    ASSERT(typeof indexA === 'number', 'index A should be number', indexA);
    ASSERT(typeof indexB === 'number', 'index B should be number', indexB); // Prune values that cant be a solution

    var A = getDomain(indexA, true);
    var B = getDomain(indexB, true);
    var minA = domain_min(A);
    var maxB = domain_max(B);
    var nA = domain_removeGtUnsafe(A, maxB);
    var nB = domain_removeLtUnsafe(B, minA);

    if (!nA || domain_isSolved(nA) || !nB || domain_isSolved(nB)) {
      TRACE(' - lte can be solved by minimizer');
      TRACE(' - either solved after pruning?', domain__debug(nA), domain__debug(nB));
      TRACE(nA ? '' : ' - A without max(B) is empty; A=', domain__debug(A), ', B=', domain__debug(B), ', max(B)=', domain_max(B), ', result:', domain_removeGtUnsafe(A, maxB));
      requestAnotherCycle = true;
      return false;
    }

    if (A !== nA) setDomain(indexA, nA);
    if (B !== nB) setDomain(indexB, nB);
    solveStack.push(function (_, force, getDomain, setDomain) {
      TRACE(' - leaf_lte; solving', indexA, '<=', indexB, '  ->  ', domain__debug(getDomain(indexA)), '<=', domain__debug(getDomain(indexB)), '  ->  ', domain_max(getDomain(indexA)), '<=', domain_min(getDomain(indexB)));
      var A = getDomain(indexA);
      var B = getDomain(indexB);
      var maxA = domain_max(A);
      var minB = domain_min(B);
      TRACE(' - maxA >? minB;', maxA, '>', minB);

      if (maxA > minB) {
        if (leafIsA) {
          var _nA2 = domain_removeGtUnsafe(A, minB);

          TRACE('   - trimmed A down to', domain__debug(_nA2));
          setDomain(indexA, _nA2);
        } else {
          var _nB2 = domain_removeLtUnsafe(B, maxA);

          TRACE('   - trimmed B down to', domain__debug(_nB2));
          setDomain(indexB, _nB2);
        }
      }

      ASSERT(getDomain(indexA));
      ASSERT(getDomain(indexB));
      ASSERT(domain_max(getDomain(indexA)) <= domain_min(getDomain(indexB)));
    });
    ml_eliminate(ml, offset, SIZEOF_C_2);
    bounty_markVar(bounty, indexA);
    bounty_markVar(bounty, indexB);
    somethingChanged();
    return true;
  }

  function leaf_some_2(ml, offset, leafIndex, otherIndex, indexA, indexB) {
    TRACE('   - leaf_some_2;', leafIndex, 'is a leaf var, A | B,', indexA, '|', indexB);
    solveStack.push(function (_, force, getDomain, setDomain) {
      TRACE(' - leaf_some_2');
      var A = getDomain(otherIndex);
      var B = getDomain(leafIndex);
      TRACE(' - solving', indexA, '|', indexB, '  ->  ', domain__debug(A), '|', domain__debug(B)); // Check if either is solved to zero, in that case force the other to non-zero.
      // if neither is zero and both have zero, force the leaf to non-zero.
      // otherwise no change because OR will be satisfied.

      if (domain_isZero(A)) {
        TRACE(' - forcing the leaf index,', leafIndex, ', to non-zero because the other var is zero');
        setDomain(leafIndex, domain_removeValue(B, 0));
      } else if (domain_isZero(B)) {
        TRACE(' - forcing the other index,', otherIndex, ', to non-zero because the leaf var was already zero');
        setDomain(otherIndex, domain_removeValue(A, 0));
      } else if (!domain_hasNoZero(A) && !domain_hasNoZero(A)) {
        TRACE(' - neither was booly solved so forcing the leaf index,', leafIndex, ', to non-zero to satisfy the OR');
        setDomain(leafIndex, domain_removeValue(B, 0));
      } else {
        TRACE(' - no change.');
      }
    });
    ml_eliminate(ml, offset, SIZEOF_C_2);
    bounty_markVar(bounty, leafIndex);
    bounty_markVar(bounty, otherIndex);
    somethingChanged();
  }

  function leaf_sum_result(ml, offset, argCount, indexR) {
    TRACE('   - leaf_sum_result;', indexR, 'is a leaf var, R = sum(', argCount, 'x ),', indexR, '= sum(...)');
    var args = markAndCollectArgs(ml, offset, argCount);
    TRACE('   - collected sum arg indexes;', args);
    TRACE('   - collected sum arg domains;', args.map(function (index) {
      return domain__debug(getDomain(index));
    }).join(', '));
    solveStack.push(function (_, force, getDomain, setDomain) {
      TRACE(' - leaf_sum_result');
      TRACE(' -', indexR, '= sum(', args, ')');
      TRACE(' -', domain__debug(getDomain(indexR)), '= sum(', args.map(function (index) {
        return domain__debug(getDomain(index));
      }).join(', '), ')');
      var sum = 0;

      for (var i = 0; i < args.length; ++i) {
        var index = args[i];
        var v = force(index);
        sum += v;
        TRACE(' - i=', i, ', index=', index, ', v=', v, ', sum now:', sum);
      }

      TRACE(' - total sum is', sum);
      var R = domain_intersectionValue(getDomain(indexR), sum);
      ASSERT(R, 'R should contain solution value');
      setDomain(indexR, R);
    });
    ml_eliminate(ml, offset, SIZEOF_C + argCount * 2 + 2);
    bounty_markVar(bounty, indexR); // Args already done in above loop

    somethingChanged();
  }

  function leaf_xnor(ml, offset, leafIndex, otherIndex, indexA, indexB) {
    TRACE('   - leaf_xnor;', leafIndex, 'is a leaf var, A !^ B,', indexA, '!^', indexB);
    ASSERT(ml_dec16(ml, offset + 1) === 2, 'should have 2 args');
    solveStack.push(function (_, force, getDomain, setDomain) {
      TRACE(' - leaf_xnor; solving', indexA, '!^', indexB, '  ->  ', domain__debug(getDomain(indexA)), '!^', domain__debug(getDomain(indexB))); // Check if a var is solved to zero, if so solve the other var to zero as well
      // check if a var is solved to non-zero, if so solve the other var to non-zero as well
      // otherwise force(A), let B follow that result

      var A = getDomain(indexA);
      var B = getDomain(indexB);

      if (domain_isZero(A)) {
        TRACE(' - forcing B to zero because A is zero');
        setDomain(indexB, domain_removeGtUnsafe(B, 0));
      } else if (domain_isZero(B)) {
        TRACE(' - forcing A to zero because B is zero');
        setDomain(indexA, domain_removeGtUnsafe(A, 0));
      } else if (domain_hasNoZero(A)) {
        TRACE(' - forcing B to non-zero because A is non-zero');
        setDomain(indexB, domain_removeValue(B, 0));
      } else if (domain_hasNoZero(B)) {
        TRACE(' - forcing A to non-zero because B is non-zero');
        setDomain(indexA, domain_removeValue(A, 0));
      } else {
        // TODO: force() and repeat above steps
        TRACE(' - neither was booly solved. forcing both to non-zero', domain__debug(domain_removeValue(A, 0)), domain__debug(domain_removeValue(B, 0))); // Non-zero gives more options? *shrug*

        setDomain(indexA, domain_removeValue(A, 0));
        setDomain(indexB, domain_removeValue(B, 0));
      }
    });
    ml_eliminate(ml, offset, SIZEOF_C_2);
    bounty_markVar(bounty, leafIndex);
    bounty_markVar(bounty, otherIndex);
    somethingChanged();
  }

  function leaf_xor(ml, offset, leafIndex, otherIndex, indexA, indexB) {
    TRACE('   - leaf_xor;', leafIndex, 'is a leaf var, A ^ B,', indexA, '^', indexB);
    solveStack.push(function (_, force, getDomain, setDomain) {
      TRACE(' - leaf_xor; solving', indexA, '^', indexB, '  ->  ', domain__debug(getDomain(indexA)), '^', domain__debug(getDomain(indexB))); // Check if either is solved to zero, in that case force the other to non-zero.
      // check if either side is non-zero. in that case force the other to zero
      // confirm that both sides are booly-solved, force them to if not.

      var A = getDomain(indexA);
      var B = getDomain(indexB);

      if (domain_isZero(A)) {
        TRACE(' - forcing B to non-zero because A is zero');
        setDomain(indexB, domain_removeValue(B, 0));
      } else if (domain_isZero(B)) {
        TRACE(' - forcing A to non-zero because B was already zero');
        setDomain(indexA, domain_removeValue(A, 0));
      } else if (domain_hasNoZero(A)) {
        TRACE(' - A was non-zero so forcing B to zero');
        setDomain(indexB, domain_removeGtUnsafe(B, 0));
      } else if (domain_hasNoZero(B)) {
        TRACE(' - B was non-zero so forcing A to zero');
        setDomain(indexA, domain_removeGtUnsafe(A, 0));
      } else {
        TRACE(' - neither was booly solved. forcing A to zero and B to non-zero');
        setDomain(indexA, domain_removeValue(A, 0));
        setDomain(indexB, domain_removeGtUnsafe(B, 0));
      }
    });
    ml_eliminate(ml, offset, SIZEOF_C_2);
    bounty_markVar(bounty, leafIndex);
    bounty_markVar(bounty, otherIndex);
    somethingChanged();
  } // ##############


  function desubset_diff(ml, diffOffset, diffArgCount, diffFirstIndex, diffFirstIndexCounts) {
    TRACE(' - desubset_diff; checking whether given DIFF at', diffOffset, 'is entirely a smaller subset than another DIFF');
    TRACE('   - argCount=', diffArgCount, ', indexA=', diffFirstIndex, ', diffFirstIndexCounts=', diffFirstIndexCounts); // A diff can superset another diff

    for (var i = 0; i < diffFirstIndexCounts; ++i) {
      var offset = bounty_getOffset(bounty, diffFirstIndex, i);

      if (offset !== diffOffset) {
        var opCode = ml_dec8(ml, offset);

        if (opCode === ML_DIFF) {
          // Diff(ABC) ⊂ diff(ABCD)  then the bigger set can be removed
          var argCount = ml_dec16(ml, offset + 1);

          if (diffArgCount > argCount) {
            // Only check if given DIFF has more args than current DIFF. always.
            // first ensure both DIFF op args are ordered
            dealiasAndSortArgs(ml, diffOffset, diffArgCount);
            dealiasAndSortArgs(ml, offset, argCount);

            if (isSubset(ml, offset, argCount, diffOffset, diffArgCount)) {
              // Note: inverted args!
              TRACE(' - deduped a DIFF subset of another DIFF! marking all args and eliminating the larger DIFF');
              markAllArgs(ml, offset, argCount); // Note: this also marks all args of DIFF1 ;)

              ml_eliminate(ml, offset, SIZEOF_C + argCount * 2);
              return true;
            }

            TRACE(' - this diff was not a subset of the other diff');
          }
        } else if (opCode === ML_ISDIFF) {
          // Diff(ABC) ⊆ R=diff?(ABCD)  then R=1 and isdiff dropped because the DIFF() will ensure it
          var _argCount = ml_dec16(ml, offset + 1);

          if (diffArgCount >= _argCount) {
            // Only check if DIFF has >= args than ISDIFF
            // first ensure both DIFF op args are ordered
            dealiasAndSortArgs(ml, diffOffset, diffArgCount);
            dealiasAndSortArgs(ml, offset, _argCount);

            if (isSubset(ml, offset, _argCount, diffOffset, diffArgCount)) {
              // Note: inverted args!
              TRACE(' - deduped a DIFF subset of an ISDIFF! Setting R=1, marking all args, and eliminating the ISDIFF');
              var indexR = readIndex(ml, offset + SIZEOF_C + _argCount * 2);
              TRACE(' - indexR=', indexR);
              var R = getDomain(indexR);
              var nR = domain_removeValue(R, 0);
              if (R !== nR) setDomain(indexR, nR);
              markAllArgs(ml, offset, _argCount); // Note: this also marks all args of DIFF1 ;)

              ml_eliminate(ml, offset, SIZEOF_C + _argCount * 2 + 2);
              return true;
            }

            TRACE(' - this DIFF was not a subset of the ISDIFF');
          }
        } else if (opCode === ML_ISSAME) {
          // DIFF(ABC) ⊆ R=SAME?(ABCD)  then R=0 and ISSAME dropped because the DIFF() _will_ negate it
          var _argCount2 = ml_dec16(ml, offset + 1);

          if (diffArgCount <= _argCount2) {
            // Only check if DIFF has fewer or equal args than ISSAME
            // first ensure both DIFF op args are ordered
            dealiasAndSortArgs(ml, diffOffset, diffArgCount);
            dealiasAndSortArgs(ml, offset, _argCount2);

            if (isSubset(ml, diffOffset, diffArgCount, offset, _argCount2)) {
              TRACE(' - deduped a DIFF subset of an ISSAME! Setting R=0, marking all args, and eliminating the ISSAME');

              var _indexR = readIndex(ml, offset + SIZEOF_C + _argCount2 * 2);

              TRACE(' - indexR=', _indexR);

              var _R = getDomain(_indexR);

              var _nR = domain_removeGtUnsafe(_R, 0);

              if (_R !== _nR) setDomain(_indexR, _nR);
              markAllArgs(ml, offset, _argCount2); // Note: this also marks all args of DIFF1 ;)

              ml_eliminate(ml, offset, SIZEOF_C + _argCount2 * 2 + 2);
              return true;
            }

            TRACE(' - this DIFF was not a subset of the ISSAME');
          }
        }
      }
    }

    TRACE(' / desubset_diff');
  }

  function desubset_nall(ml, nallOffset, nallArgCount, nallFirstIndex, nallFirstIndexCounts) {
    TRACE(' - desubset_nall; checking whether given NALL at', nallOffset, 'is entirely a smaller subset than another NALL');
    TRACE('   - argCount=', nallArgCount, ', indexA=', nallFirstIndex, ', nallFirstIndexCounts=', nallFirstIndexCounts); // A nall can subset another nall

    for (var i = 0; i < nallFirstIndexCounts; ++i) {
      var offset = bounty_getOffset(bounty, nallFirstIndex, i);

      if (offset !== nallOffset) {
        var opCode = ml_dec8(ml, offset);

        if (opCode === ML_NALL) {
          // Nall(ABC) ⊂ nall(ABCD)  then the bigger set can be removed
          var argCount = ml_dec16(ml, offset + 1);

          if (nallArgCount < argCount) {
            // Only check if given NALL has fewer args than current NALL. always.
            // first ensure both NALL op args are ordered
            dealiasAndSortArgs(ml, nallOffset, nallArgCount);
            dealiasAndSortArgs(ml, offset, argCount);

            if (isSubset(ml, nallOffset, nallArgCount, offset, argCount)) {
              TRACE(' - deduped a NALL subset of another NALL! marking all args and eliminating the larger NALL');
              markAllArgs(ml, offset, argCount); // Note: this also marks all args of NALL1 ;)

              ml_eliminate(ml, offset, SIZEOF_C + argCount * 2);
              return true;
            }

            TRACE(' - this nall was not a subset of the other nall');
          }
        } else if (opCode === ML_ISNALL) {
          // Nall(ABC) ⊆ R=nall?(ABCD)  then R=1 and isnall dropped because the NALL() will ensure it
          var _argCount3 = ml_dec16(ml, offset + 1);

          if (nallArgCount <= _argCount3) {
            // Only check if NALL has fewer or equal args than ISNALL
            // first ensure both NALL op args are ordered
            dealiasAndSortArgs(ml, nallOffset, nallArgCount);
            dealiasAndSortArgs(ml, offset, _argCount3);

            if (isSubset(ml, nallOffset, nallArgCount, offset, _argCount3)) {
              TRACE(' - deduped a NALL subset of an ISNALL! Setting R=1, marking all args, and eliminating the ISNALL');
              var indexR = readIndex(ml, offset + SIZEOF_C + _argCount3 * 2);
              TRACE(' - indexR=', indexR);
              var R = getDomain(indexR);
              var nR = domain_removeValue(R, 0);
              if (R !== nR) setDomain(indexR, nR);
              markAllArgs(ml, offset, _argCount3); // Note: this also marks all args of NALL1 ;)

              ml_eliminate(ml, offset, SIZEOF_C + _argCount3 * 2 + 2);
              return true;
            }

            TRACE(' - this NALL was not a subset of the ISNALL');
          }
        } else if (opCode === ML_ISALL) {
          // NALL(ABC) ⊆ R=ALL?(ABCD)  then R=0 and ISALL dropped because the NALL() _will_ negate it
          var _argCount4 = ml_dec16(ml, offset + 1);

          if (nallArgCount <= _argCount4) {
            // Only check if NALL has fewer or equal args than ISALL
            // first ensure both NALL op args are ordered
            dealiasAndSortArgs(ml, nallOffset, nallArgCount);
            dealiasAndSortArgs(ml, offset, _argCount4);

            if (isSubset(ml, nallOffset, nallArgCount, offset, _argCount4)) {
              TRACE(' - deduped a NALL subset of an ISALL! Setting R=0, marking all args, and eliminating the ISALL');

              var _indexR2 = readIndex(ml, offset + SIZEOF_C + _argCount4 * 2);

              TRACE(' - indexR=', _indexR2);

              var _R2 = getDomain(_indexR2);

              var _nR2 = domain_removeGtUnsafe(_R2, 0);

              if (_R2 !== _nR2) setDomain(_indexR2, _nR2);
              markAllArgs(ml, offset, _argCount4); // Note: this also marks all args of NALL1 ;)

              ml_eliminate(ml, offset, SIZEOF_C + _argCount4 * 2 + 2);
              return true;
            }

            TRACE(' - this NALL was not a subset of the ISALL');
          }
        }
      }
    }
  }

  function desubset_some(ml, someOffset, someArgCount, someFirstIndex, someFirstIndexCounts) {
    TRACE(' - desubset_some; checking whether given SOME at', someOffset, 'is entirely a smaller subset than another SOME');
    TRACE('   - argCount=', someArgCount, ', indexA=', someFirstIndex, ', someFirstIndexCounts=', someFirstIndexCounts); // A some can subset another some

    for (var i = 0; i < someFirstIndexCounts; ++i) {
      var offset = bounty_getOffset(bounty, someFirstIndex, i);

      if (offset !== someOffset) {
        var opCode = ml_dec8(ml, offset);

        if (opCode === ML_SOME) {
          // Some(ABC) ⊂ some(ABCD)  then the bigger set can be removed
          var argCount = ml_dec16(ml, offset + 1);

          if (someArgCount < argCount) {
            // Only check if given SOME has fewer args than current SOME. always.
            // first ensure both SOME op args are ordered
            dealiasAndSortArgs(ml, someOffset, someArgCount);
            dealiasAndSortArgs(ml, offset, argCount);

            if (isSubset(ml, someOffset, someArgCount, offset, argCount)) {
              TRACE(' - deduped a SOME subset of another SOME! marking all args and eliminating the larger SOME');
              markAllArgs(ml, offset, argCount); // Note: this also marks all args of SOME1 ;)

              ml_eliminate(ml, offset, SIZEOF_C + argCount * 2);
              somethingChanged();
              return true;
            }

            TRACE(' - this SOME was not a subset of the other SOME');
          }
        } else if (opCode === ML_ISSOME) {
          // Some(ABC) ⊆ R=some?(ABCD)  then R=1 and issome dropped because the SOME() will ensure it
          var _argCount5 = ml_dec16(ml, offset + 1);

          if (someArgCount <= _argCount5) {
            // Only check if SOME has fewer or equal args than ISSOME
            // first ensure both SOME op args are ordered
            dealiasAndSortArgs(ml, someOffset, someArgCount);
            dealiasAndSortArgs(ml, offset, _argCount5);

            if (isSubset(ml, someOffset, someArgCount, offset, _argCount5)) {
              TRACE(' - deduped a SOME subset of an ISSOME! Setting R=1, marking all args, and eliminating the ISSOME');
              var indexR = readIndex(ml, offset + SIZEOF_C + _argCount5 * 2);
              TRACE(' - indexR=', indexR);
              var R = getDomain(indexR);
              var nR = domain_removeValue(R, 0);
              if (R !== nR) setDomain(indexR, nR);
              markAllArgs(ml, offset, _argCount5); // Note: this also marks all args of SOME1 ;)

              ml_eliminate(ml, offset, SIZEOF_C + _argCount5 * 2 + 2);
              somethingChanged();
              return true;
            }

            TRACE(' - this some was not a subset of the issome');
          }
        } else if (opCode === ML_ISNONE) {
          // SOME(ABC) ⊆ R=NONE?(ABCD)  then R=0 and ISNONE dropped because the SOME() _will_ negate it
          var _argCount6 = ml_dec16(ml, offset + 1);

          if (someArgCount <= _argCount6) {
            // Only check if SOME has fewer or equal args than ISNONE
            // first ensure both SOME op args are ordered
            dealiasAndSortArgs(ml, someOffset, someArgCount);
            dealiasAndSortArgs(ml, offset, _argCount6);

            if (isSubset(ml, someOffset, someArgCount, offset, _argCount6)) {
              TRACE(' - deduped a SOME subset of an ISNONE! Setting R=0, marking all args, and eliminating the ISNONE');

              var _indexR3 = readIndex(ml, offset + SIZEOF_C + _argCount6 * 2);

              TRACE(' - indexR=', _indexR3);

              var _R3 = getDomain(_indexR3);

              var _nR3 = domain_removeGtUnsafe(_R3, 0);

              if (_R3 !== _nR3) setDomain(_indexR3, _nR3);
              markAllArgs(ml, offset, _argCount6); // Note: this also marks all args of SOME1 ;)

              ml_eliminate(ml, offset, SIZEOF_C + _argCount6 * 2 + 2);
              somethingChanged();
              return true;
            }

            TRACE(' - this SOME was not a subset of the ISNONE');
          }
        }
      }
    }
  }

  function isSubset(ml, someOffset1, argCount1, someOffset2, argCount2) {
    // Now "zip" and confirm that all args in SOME1 are present by SOME2.
    var pos1 = 0;
    var pos2 = 0;
    var index1 = ml_dec16(ml, someOffset1 + SIZEOF_C + pos1 * 2);
    var index2 = 0;

    while (pos2 < argCount2) {
      index2 = ml_dec16(ml, someOffset2 + SIZEOF_C + pos2 * 2);

      while (index1 === index2) {
        ++pos1;

        if (pos1 >= argCount1) {
          return true;
        }

        index1 = ml_dec16(ml, someOffset1 + SIZEOF_C + pos1 * 2);
      }

      ++pos2;
    }

    return false;
  }

  function dealiasAndSortArgs(ml, offset, argCount) {
    TRACE(' - dealiasAndSortArgs; sorting and dealiasing', argCount, 'args starting at', offset); // First de-alias all args

    for (var i = 0; i < argCount; ++i) {
      var argOffset = offset + SIZEOF_C + i * 2;
      var actual = ml_dec16(ml, argOffset);
      var alias = getAlias(actual);
      if (actual !== alias) ml_enc16(ml, argOffset, alias);
    } // Now sort them


    ml_heapSort16bitInline(ml, offset + SIZEOF_C, argCount);
  } // ##############


  function trick_sum_to_nall(ml, offset, argCount, indexR) {
    // [0 0 n-1 n-1]=sum([01] [01] [01]   =>   nall(...)
    TRACE('   - trick_sum_to_nall');
    TRACE_MORPH('[0 0 n-1 n-1]=sum(A:[01] B:[01] C:[01] ...)', 'nall(A B C ...)');
    TRACE('   - indexR:', indexR, ', R:', domain__debug(getDomain(indexR)));
    TRACE('   -', ml__debug(ml, offset, 1, problem));
    ASSERT(getDomain(indexR) === domain_createRange(0, argCount - 1) && domain_min(getDomain(indexR)) === 0 && domain_max(getDomain(indexR)) === argCount - 1);
    var args = markAndCollectArgs(ml, offset, argCount);
    TRACE('   - args:', args, ', doms:', args.map(getDomain).map(domain__debug).join(', '));
    ASSERT(args.map(getDomain).every(domain_isBool), 'all args should be bool');
    solveStack.push(function (_, force, getDomain, setDomain) {
      TRACE(' - trick_sum_to_nall');
      TRACE(' -', indexR, '= sum(', args, ')');
      TRACE(' -', domain__debug(getDomain(indexR)), '= sum(', args.map(function (index) {
        return domain__debug(getDomain(index));
      }), ')');
      var R = getDomain(indexR);
      TRACE(' - scan first');
      var current = 0;

      for (var i = 0; i < args.length; ++i) {
        var index = args[i];
        var D = getDomain(index);
        var vD = domain_getValue(D);
        if (vD >= 0) current += vD;
      }

      var vR = domain_min(domain_removeLtUnsafe(R, current)); // "R must be at least the current sum of constant args"

      var remaining = vR - current;
      TRACE(' - args that are solved currently sum to', current, ', R=', domain__debug(R), ', so there is', remaining, 'to be added');

      for (var _i2 = 0; _i2 < args.length; ++_i2) {
        var _index2 = args[_i2];

        var _D = getDomain(_index2);

        if (!domain_isSolved(_D)) {
          if (remaining > 0) {
            _D = domain_removeValue(_D, 0);
            --remaining;
          } else {
            _D = domain_removeValue(_D, 1);
          } // SUM requires all args to solve. let them pick any value from what remains.


          force(_index2, _D);
        }
      }

      setDomain(indexR, domain_intersectionValue(R, vR));
      ASSERT(getDomain(indexR));
      ASSERT(domain_isSolved(getDomain(indexR)));
      ASSERT(domain_getValue(getDomain(indexR)) === args.reduce(function (a, b) {
        return a + force(b);
      }, 0));
    }); // From sum to nall.

    ml_cr2c(ml, offset, argCount, ML_NALL, args);
    bounty_markVar(bounty, indexR); // Args already done in above loop

    somethingChanged();
  }

  function trick_some_sum(ml, offset, argCount, indexR) {
    // [1 1 n n]=sum([01] [01] [01]   ->   nall(...)
    TRACE('   - trick_some_sum; [1 1 n n]=sum([01] [01] [01] ...) is actually a SOME', indexR);
    var args = markAndCollectArgs(ml, offset, argCount);
    solveStack.push(function (_, force, getDomain, setDomain) {
      TRACE(' - trick_some_sum');
      TRACE(' - some(A B);', indexR, '= sum(', args, ')  ->  ', domain__debug(getDomain(indexR)), '= sum(', args.map(function (index) {
        return domain__debug(getDomain(index));
      }), ')'); // First make sure at least one arg is nonzero. for once if none already is.

      var none = true;
      var booly = -1;

      for (var i = 0; i < argCount; ++i) {
        var index = args[i];
        var D = getDomain(index);

        if (domain_hasNoZero(D)) {
          none = false;
          break;
        }

        if (!domain_isZero(D)) {
          ASSERT(domain_isBooly(D));
          booly = index;
        }
      }

      if (none) {
        ASSERT(booly >= 0);

        var _D2 = getDomain(booly);

        _D2 = domain_removeValue(_D2, 0);
        setDomain(booly, _D2);
        ASSERT(_D2);
      } // Now collect the sum. do it in a new loop because it's just simpler that way.
      // force all the args because otherwise the sum might be violated


      var sum = 0;

      for (var _i3 = 0; _i3 < argCount; ++_i3) {
        sum += force(args[_i3]);
      } // Set R to the sum of all constants


      var R = getDomain(indexR);
      R = domain_intersectionValue(R, sum);
      setDomain(indexR, R);
      ASSERT(R);
    }); // From sum to some.

    ml_enc8(ml, offset, ML_SOME);
    ml_enc16(ml, offset + 1, argCount);

    for (var i = 0; i < argCount; ++i) {
      ml_enc16(ml, offset + SIZEOF_C + i * 2, args[i]);
    }

    ml_compileJumpSafe(ml, offset + SIZEOF_C + argCount * 2, 2); // Result var (16bit). for the rest some is same as sum

    bounty_markVar(bounty, indexR); // Args already done in above loop

    somethingChanged();
  }

  function trick_isall_ltelhs_1shared(ml, lteOffset, indexR, countsR) {
    var indexS = readIndex(ml, lteOffset + OFFSET_C_B);
    TRACE('trick_isall_ltelhs_1shared');
    TRACE(' - with only R shared on an isall[2]:');
    TRACE('   - R <= S, R = all?(A B)      =>      some(S | nall?(A B))');
    TRACE(' - indexes:', indexR, '<=', indexS);
    TRACE(' - domains:', getDomain(indexR), '<=', getDomain(indexS));
    TRACE(' - metaFlags:', bounty__debugMeta(bounty, indexR), '<=', bounty__debugMeta(bounty, indexS)); // The next asserts should have been verified by the bounty hunter, so they are only verified in ASSERTs

    ASSERT(countsR === 2, 'R should be a leaf var with these two constraints');
    ASSERT(countsR === getCounts(bounty, indexR), 'correct value?');
    ASSERT(getMeta(bounty, indexR) === (BOUNTY_FLAG_LTE_LHS | BOUNTY_FLAG_ISALL_RESULT), 'A be an lte lhs and isall result var');
    ASSERT(ml_dec8(ml, lteOffset) === ML_LTE, 'lteOffset should be lte');
    ASSERT(ml_dec16(ml, lteOffset + OFFSET_C_A) === indexR, 'shared index should be lhs of lteOffset');

    if (!domain_isBool(getDomain(indexR, true)) || !domain_isBool(getDomain(indexS, true))) {
      TRACE(' - R or S wasnt bool, bailing');
      return false;
    }

    var offset1 = bounty_getOffset(bounty, indexR, 0);
    var offset2 = bounty_getOffset(bounty, indexR, 1);
    var isallOffset = offset1 === lteOffset ? offset2 : offset1;
    ASSERT(ml_dec8(ml, isallOffset) === ML_ISALL);
    ASSERT(readIndex(ml, isallOffset + OFFSET_C_R) === indexR);

    if (ml_dec16(ml, isallOffset + 1) !== 2) {
      TRACE(' - isall did not have 2 args, bailing');
      return false;
    }

    var indexA = readIndex(ml, isallOffset + OFFSET_C_A);
    var indexB = readIndex(ml, isallOffset + OFFSET_C_B);

    if (!domain_isBool(getDomain(indexA, true)) || !domain_isBool(getDomain(indexB, true))) {
      TRACE(' - A or B wasnt bool, bailing');
      return false;
    }

    TRACE_MORPH('R <= S, R = all?(A B)', 'S | nall?(A B)');
    TRACE(' - change the isall to an isnall, change the LTE to an OR');
    ml_cr2cr2(ml, isallOffset, 2, ML_ISNALL, indexA, indexB, indexR);
    ml_c2c2(ml, lteOffset, 2, ML_SOME, indexR, indexS);
    bounty_markVar(bounty, indexR);
    bounty_markVar(bounty, indexS);
    bounty_markVar(bounty, indexA);
    bounty_markVar(bounty, indexB);
    somethingChanged();
    return true;
  }

  function trick_isall_implhs_1shared(ml, impOffset, indexR, countsR) {
    var indexS = readIndex(ml, impOffset + OFFSET_C_B);
    TRACE('trick_isall_implhs_1shared');
    TRACE(' - with only R shared on an isall[2]:');
    TRACE('   - R -> S, R = all?(A B)      =>      some(S | nall?(A B))');
    TRACE(' - indexes:', indexR, '<=', indexS);
    TRACE(' - domains:', getDomain(indexR), '<=', getDomain(indexS));
    TRACE(' - metaFlags:', bounty__debugMeta(bounty, indexR), '<=', bounty__debugMeta(bounty, indexR)); // The next asserts should have been verified by the bounty hunter, so they are only verified in ASSERTs

    ASSERT(countsR === 2, 'R should be a leaf var with these two constraints');
    ASSERT(countsR === getCounts(bounty, indexR), 'correct value?');
    ASSERT(getMeta(bounty, indexR) === (BOUNTY_FLAG_IMP_LHS | BOUNTY_FLAG_ISALL_RESULT), 'A be an imp lhs and isall result var');
    ASSERT(ml_dec8(ml, impOffset) === ML_IMP, 'impOffset should be imp');
    ASSERT(ml_dec16(ml, impOffset + OFFSET_C_A) === indexR, 'shared index should be lhs of impOffset');

    if (!domain_isBool(getDomain(indexR, true)) || !domain_isBool(getDomain(indexS, true))) {
      TRACE(' - R or S wasnt bool, bailing');
      return false;
    }

    var offset1 = bounty_getOffset(bounty, indexR, 0);
    var offset2 = bounty_getOffset(bounty, indexR, 1);
    var isallOffset = offset1 === impOffset ? offset2 : offset1;
    ASSERT(ml_dec8(ml, isallOffset) === ML_ISALL);
    ASSERT(readIndex(ml, isallOffset + OFFSET_C_R) === indexR);

    if (ml_dec16(ml, isallOffset + 1) !== 2) {
      TRACE(' - isall did not have 2 args, bailing');
      return false;
    }

    if (!domain_isBool(getDomain(indexA, true)) || !domain_isBool(getDomain(indexB, true))) {
      TRACE(' - A or B wasnt bool, bailing');
      return false;
    }

    TRACE_MORPH('R -> S, R = all?(A B)', 'S | nall?(A B)');
    TRACE(' - change the isall to a nall, change the imp to an or');
    var indexA = readIndex(ml, isallOffset + OFFSET_C_A);
    var indexB = readIndex(ml, isallOffset + OFFSET_C_B);
    ml_cr2cr2(ml, isallOffset, 2, ML_ISNALL, indexA, indexB, indexR);
    ml_c2c2(ml, impOffset, 2, ML_SOME, indexR, indexS);
    bounty_markVar(bounty, indexR);
    bounty_markVar(bounty, indexS);
    bounty_markVar(bounty, indexA);
    bounty_markVar(bounty, indexB);
    somethingChanged();
    return true;
  }

  function trick_isall_ltelhs_2shared(ml, lteOffset, indexR, countsR) {
    var indexA = readIndex(ml, lteOffset + OFFSET_C_B);
    TRACE('trick_isall_ltelhs_2shared');
    TRACE(' - with R and an arg shared:');
    TRACE('   - R <= A, R = all?(A B ...)      ->      R = all?(A B ...)');
    TRACE('   - (the isall subsumes the lte, regardless of other constraints)'); // TRACE(' - with only R shared:');
    // TRACE('   - R <= A, R = all?(B C)          ->      some(C nall?(A B))');
    // TRACE('   - (when R is leaf, only A=1 B=1 C=0 is false)');

    TRACE(' - indexes:', indexR, '<=', indexA);
    TRACE(' - domains:', getDomain(indexR), '<=', getDomain(indexA));
    TRACE(' - metaFlags:', bounty__debugMeta(bounty, indexR), '<=', bounty__debugMeta(bounty, indexR)); // The next asserts should have been verified by the bounty hunter, so they are only verified in ASSERTs

    ASSERT(countsR > 1, 'the indexR should be part of at least two constraints');
    ASSERT(countsR === getCounts(bounty, indexR), 'correct value?');
    ASSERT(hasFlags(getMeta(bounty, indexR), BOUNTY_FLAG_LTE_LHS | BOUNTY_FLAG_ISALL_RESULT), 'A must at least be an lte lhs and isall result var');
    ASSERT(ml_dec8(ml, lteOffset) === ML_LTE, 'lteOffset should be lte');
    ASSERT(ml_dec16(ml, lteOffset + OFFSET_C_A) === indexR, 'shared index should be lhs of lteOffset');
    var toCheck = Math.min(countsR, BOUNTY_MAX_OFFSETS_TO_TRACK); // Note: it's not guaranteed that we'll actually see an isall in this loop
    // if countsR is higher than the max number of offsets tracked by bounty
    // in that case nothing happens and the redundant constraint persists. no biggie

    for (var i = 0; i < toCheck; ++i) {
      TRACE('   - fetching #', i, '/', toCheck, '(', countsR, '||', BOUNTY_MAX_OFFSETS_TO_TRACK, ')');
      var offset = bounty_getOffset(bounty, indexR, i);
      TRACE('   - #' + i, ', offset =', offset);

      if (offset !== lteOffset) {
        var op = ml_dec8(ml, offset);

        if (op === ML_ISALL) {
          if (_trick_isall_ltelhs_2shared(lteOffset, offset, indexR, indexA)) return true;
        }
      }
    }

    TRACE(' - trick_isall_ltelhs_2shared changed nothing');
    return false;
  }

  function _trick_isall_ltelhs_2shared(lteOffset, isallOffset, indexR, indexA) {
    // R <= A, R = all?(A B C ...)    =>     R = all?(A B C ...)   (drop lte)
    // need to search the isall for the A arg here
    ASSERT(ml_dec8(ml, isallOffset) === ML_ISALL, 'should be isall');
    var argCount = ml_dec16(ml, isallOffset + 1);
    var indexS = readIndex(ml, isallOffset + SIZEOF_C + argCount * 2);
    TRACE('     - isall with an argCount of', argCount, ', indexR=', indexS, '=indexR=', indexR, 'cross checking all args to match', indexA);
    ASSERT(indexS === indexR, 'R should (at least) be result of isall'); // Scan for any arg index == A

    for (var i = 0; i < argCount; ++i) {
      var argIndex = readIndex(ml, isallOffset + SIZEOF_C + i * 2);

      if (argIndex === indexA) {
        TRACE_MORPH('R <= A, R = all?(A ...)', 'R = all?(A ...)', 'The isall subsumes the lte');
        TRACE('     - arg index is indexA, match. this is R <= A, R = all?(A ...) so eliminate the lte');
        ml_eliminate(ml, lteOffset, SIZEOF_C_2);
        bounty_markVar(bounty, indexR);
        bounty_markVar(bounty, indexA);
        somethingChanged();
        return true;
      }
    }

    return false;
  }

  function trick_implhs_isall_2shared(ml, impOffset, indexA, countsA) {
    TRACE('trick_implhs_isall_2shared', indexA, 'at', impOffset, 'metaFlags:', bounty__debugMeta(bounty, indexA), '`S -> A, S = all?(A B ...)   ->   S = all?(A B ...)`');
    TRACE(' - imp:', indexA, '->', readIndex(ml, impOffset + OFFSET_C_B), '  =>  ', domain__debug(getDomain(indexA, true)), '->', domain__debug(getDomain(readIndex(ml, impOffset + OFFSET_C_B), true)));
    TRACE('   - S -> A, S = all?(A B)   =>   S = all?(A B)');
    TRACE('   - (the isall subsumes the implication, regardless of other constraints)'); // The next asserts should have been verified by the bounty hunter, so they are only verified in ASSERTs

    ASSERT(countsA > 1, 'the indexA should only be part of two constraints', countsA, bounty__debugMeta(bounty, indexA));
    ASSERT(countsA === getCounts(bounty, indexA), 'correct value?', countsA === getCounts(bounty, indexA));
    ASSERT(hasFlags(getMeta(bounty, indexA), BOUNTY_FLAG_IMP_LHS | BOUNTY_FLAG_ISALL_RESULT), 'A must at least be an imp lhs and isall result var');
    ASSERT(ml_dec8(ml, impOffset) === ML_IMP, 'impOffset should be imp', ml__opName(ml_dec8(ml, impOffset)));
    ASSERT(ml_dec16(ml, impOffset + OFFSET_C_A) === indexA, 'shared index should be lhs of impOffset');
    var indexB = readIndex(ml, impOffset + OFFSET_C_B);
    var toCheck = Math.min(countsA, BOUNTY_MAX_OFFSETS_TO_TRACK); // Note: it's not guaranteed that we'll actually see an isall in this loop
    // if countsA is higher than the max number of offsets tracked by bounty
    // in that case nothing happens and the redundant constraint persists. no biggie

    for (var i = 0; i < toCheck; ++i) {
      TRACE('   - fetching #', i, '/', toCheck, '(', countsA, '|', BOUNTY_MAX_OFFSETS_TO_TRACK, ')');
      var offset = bounty_getOffset(bounty, indexA, i);
      TRACE('   - #' + i, ', offset =', offset);

      if (offset !== impOffset) {
        var op = ml_dec8(ml, offset);

        if (op === ML_ISALL) {
          TRACE(' - Found the isall...');
          if (_trick_implhs_isall_2shared(impOffset, offset, indexA, indexB)) return true;
        }
      }
    }

    TRACE(' - end of trick_implhs_isall_2shared');
    return false;
  }

  function _trick_implhs_isall_2shared(impOffset, isallOffset, indexA, indexB) {
    // A -> B, A = all?(B C D ...)     =>    drop imp
    TRACE(' - _trick_implhs_isall_2shared; A -> B, A = all?(B C D ...)    =>    drop imp');
    ASSERT(ml_dec8(ml, isallOffset) === ML_ISALL, 'should be isall'); // TRACE(ml__debug(ml, isallOffset, 1, problem, true));

    var argCount = ml_dec16(ml, isallOffset + 1);
    var indexR = readIndex(ml, isallOffset + SIZEOF_C + argCount * 2);
    TRACE('     - isall with an argCount of', argCount, ', indexR=', indexR, '=indexA=', indexA, ', cross-checking all args to match', indexB);
    ASSERT(indexA === indexR, 'A should be R, should be asserted by bounty'); // Scan for any arg index == B

    for (var i = 0; i < argCount; ++i) {
      var argIndex = readIndex(ml, isallOffset + SIZEOF_C + i * 2);

      if (argIndex === indexB) {
        TRACE_MORPH('R -> A, R = all?(A ...)', 'R = all?(A ...)', 'The isall subsumes the implication');
        TRACE('     - arg index is indexB, match. this is R -> A, R = all?(A ...) so eliminate the imp');
        ml_eliminate(ml, impOffset, SIZEOF_C_2);
        bounty_markVar(bounty, indexA);
        bounty_markVar(bounty, indexB);
        somethingChanged();
        return true;
      }
    }

    return false;
  }

  function trick_isall_lterhs_entry(indexS, lteOffset, counts) {
    // A <= S, S = all?(B C...)    ->    A <= B, A <= C
    var offset1 = bounty_getOffset(bounty, indexS, 0);
    var offset2 = bounty_getOffset(bounty, indexS, 1);
    TRACE('trick_isall_lterhs_entry; ', indexS, 'at', lteOffset, '->', offset1, offset2, '` A <= S, S = all?(B C...)    ->    A <= B, A <= C`');
    ASSERT(lteOffset === offset1 || lteOffset === offset2, 'expecting current offset to be one of the two offsets found', lteOffset, indexS);
    var isallOffset = lteOffset === offset1 ? offset2 : offset1; // This stuff should have been checked by the bounty hunter, so we tuck them in ASSERTs

    ASSERT(ml_dec8(ml, lteOffset) === ML_LTE, 'lteOffset should be an lte');
    ASSERT(ml_dec8(ml, isallOffset) === ML_ISALL, 'isall offset should be either isall op');
    ASSERT(getMeta(bounty, indexS) === (BOUNTY_FLAG_LTE_RHS | BOUNTY_FLAG_ISALL_RESULT), 'kind of redundant, but this is what bounty should have yielded for this var');
    ASSERT(counts === 2, 'S should only appear in two constraints');
    ASSERT((ml_dec8(ml, isallOffset) === ML_ISALL ? readIndex(ml, isallOffset + SIZEOF_C + ml_dec16(ml, isallOffset + 1) * 2) : readIndex(ml, isallOffset + 5)) === indexS, 'S should the result of the isall'); // We can replace an isall and lte with ltes on the args of the isall
    // A <= S, S = isall(C D)   ->    A <= C, A <= D
    // note that A amust be strict bool and A must have a 0 for this to be safe. S is our shared var here.
    // [01] <= [01], [01] = isall(....)
    // if you dont apply this condition:
    // [0 0 5 5 9 9] <= [0 0 9 9], [0 0 9 9] = isall([55], [66])
    // after the morph A _must_ be 0 or 5 while before it could also be 9.

    var indexA = readIndex(ml, lteOffset + OFFSET_C_A);
    var A = getDomain(indexA, true);
    ASSERT(indexS === readIndex(ml, lteOffset + OFFSET_C_B), 'S should be rhs of lte');
    var S = getDomain(indexS, true); // Mostly A will be [01] but dont rule out valid cases when A=0 or A=1
    // A or C (or both) MUST be boolean bound or this trick may be bad (A=100,S=100,C=1,D=1 -> 100<=10,100<=10 while it should pass)

    if (domain_max(A) > 1 && domain_max(S) > 1) {
      TRACE(' - neither A nor S was boolean bound, bailing', domain__debug(A), domain__debug(S));
      return false;
    }

    if (domain_hasNoZero(S)) {
      // (dead code because minifier should eliminate an isall when R>=1)
      TRACE('- S has no zero which it would need to reflect any solution as a leaf, bailing', domain__debug(S)); // (unless the isall was already solved, but the minimizer should take care of that)

      requestAnotherCycle = true;
      return false;
    }

    if (domain_max(A) > domain_max(S)) {
      // (dead code because minifier should eliminate an isall when R=0)
      TRACE(' - max(A) > max(S) so there is a value in A that S couldnt satisfy A<=S so we must bail', domain__debug(A), domain__debug(S)); // We can only trick if S can represent any valuation of A and there is a reject possible so no
      // note that this shouldnt happen when the minimizer runs to the max, but could in single cycle mode

      requestAnotherCycle = true;
      return false;
    }

    TRACE(' - A and S are okay proceeding with morph, A:', domain__debug(A), 'S:', domain__debug(S));
    ASSERT(ml_dec8(ml, isallOffset) === ML_ISALL, 'bounty should have asserted this');
    var argCount = ml_dec16(ml, isallOffset + 1);
    TRACE(' - an isall starting at', isallOffset, 'and has', argCount, 'args; rewriting A <= S, S=isall(X Y Z ...)  ->  A <= X, A <= Y, A <= Z, ...');
    var maxA = domain_max(A);

    for (var i = 0; i < argCount; ++i) {
      var index = readIndex(ml, isallOffset + SIZEOF_C + i * 2);
      var domain = getDomain(index, true);

      if (domain_max(domain) < maxA) {
        TRACE(' - there is an isall arg whose max is lower than max(A), this leads to a lossy morph so we must bail', i, index, domain__debug(domain), '<', domain__debug(A));
        return false;
      }
    }

    if (argCount < 2) {
      TRACE(' - argcount < 2, so a bug or an alias. ignoring that here. bailing');
      return false;
    } // First encode the isall args beyond the second one (if any) into recycled spaces


    if (argCount > 2) {
      var proceed = trick_isall_lterhs_entry_excess(ml, isallOffset, argCount, indexA);
      if (!proceed) return false;
    } // Now morph the first two args into the existing lte and isall (of same size)


    var indexX = readIndex(ml, isallOffset + OFFSET_C_A);
    var indexY = readIndex(ml, isallOffset + OFFSET_C_B);
    TRACE(' -  A <= S, S=isall(X Y, ...(already done the rest))   ->    A <= X, A <= Y'); // Must mark all affected vars. their bounty data is probably obsolete now.
    // (collect the isall before morphing it!)

    bounty_markVar(bounty, indexA);
    bounty_markVar(bounty, indexS);
    var isallArgs = markAndCollectArgs(ml, isallOffset, argCount);
    ASSERT(isallArgs[0] === indexX, 'x should be collected');
    ASSERT(isallArgs[1] === indexY, 'y should be collected');
    TRACE(' - isall args:', isallArgs, ', and from the lte A=', indexA, ', S=', indexS); // Compile A<=left and A<=right over the existing two offsets

    ml_c2c2(ml, lteOffset, 2, ML_LTE, indexA, indexX);
    ml_cr2c2(ml, isallOffset, 2, ML_LTE, indexA, indexY);
    TRACE('   - deferring', indexS, 'will be gt', indexA, 'and the result of an isall');
    solveStack.push(function (_, force, getDomain, setDomain) {
      // Note: we cut out indexS so that's what we restore here!
      TRACE(' - trick_isall_lterhs_entry; patching index', indexS);
      TRACE('   -', indexA, '<=', indexS, '  ->  ', domain__debug(getDomain(indexA)), '<=', domain__debug(getDomain(indexS)));
      TRACE('   -', indexS, '= all?(', isallArgs, ')  ->  ', domain__debug(getDomain(indexS)), '= all?(', isallArgs.map(function (index) {
        return domain__debug(getDomain(index));
      }), ')');
      var S = getDomain(indexS);
      var A = getDomain(indexA); // Was A <= S so S can't contain any value lower than max(A)

      S = domain_removeLtUnsafe(S, domain_max(A));
      ASSERT(S, 'should not be empty here'); // Was S = isall(X Y ...args) so force any arg that is not yet booly-solved until we find one that's 0

      var someZero = false;

      for (var _i4 = 0; _i4 < isallArgs.length; ++_i4) {
        var D = getDomain(isallArgs[_i4]);

        if (domain_isZero(D) || !domain_hasNoZero(S) && force(D) === 0) {
          TRACE('  - index', isallArgs[_i4], 'was', domain__debug(D), 'now', domain__debug(getDomain(isallArgs[_i4])), ', ends up zero so it fails the isall so S must be 0'); // Either D was already zero, or it was booly and then forced to zero. it fails the isall so S=0

          someZero = true;
          break;
        }
      }

      TRACE(' -', someZero ? 'at least one' : 'no', 'arg was found to be zero');

      if (someZero) {
        S = domain_removeGtUnsafe(S, 0);
      } else {
        S = domain_removeValue(S, 0);
      }

      ASSERT(S, 'S should not be empty here');
      setDomain(indexS, S);
    });
    somethingChanged();
    return true;
  }

  function trick_isall_lterhs_entry_excess(ml, isallOffset, argCount, indexA) {
    // Isall has four or more args
    // A <= S, S=isall(X Y Z ...)  ->  A <= X, A <= Y, A <= Z, ...
    // note: this function only compiles the args from Z (the third isall arg) onward
    TRACE(' - trick_isall_lterhs_entry_excess. Attempting to recycle space to stuff', argCount - 2, 'lte constraints');
    ASSERT(argCount > 2, 'this function should only be called for 4+ isall args'); // We have to recycle some space now. we wont know whether we can
    // actually do the morph until we've collected enough space for it.
    // we'll use lteOffset and isallOffset to compile the last 2 args so only need space for the remaining ones

    var toRecycle = argCount - 2; // Start by collecting toRecycle recycled spaces

    var bins = ml_getRecycleOffsets(ml, 0, toRecycle, SIZEOF_C_2);

    if (!bins) {
      TRACE(' - Was unable to find enough free space to fit', argCount, 'ltes, bailing');
      return false;
    }

    TRACE(' - Found', bins.length, 'jumps (', bins, ') which can host (at least)', toRecycle, 'lte constraints. Compiling them now'); // Okay, now we'll morph. be careful about clobbering existing indexes... start with
    // last address to make sure jumps dont clobber existing jump offsets in the bin

    var i = 0;

    while (i < toRecycle) {
      var currentOffset = bins.pop();
      ASSERT(ml_dec8(ml, currentOffset) === ML_JMP, 'should only get jumps here'); // Might trap a case where we clobber

      var size = ml_getOpSizeSlow(ml, currentOffset);
      ASSERT(size >= SIZEOF_C_2, 'this is what we asked for');

      do {
        var indexB = readIndex(ml, isallOffset + SIZEOF_C + (i + 2) * 2); // Note: i+2 because we skip the first two args. they are done by caller

        TRACE('  - compiling lte:', indexA, '<=', indexB, ' -> ', domain__debug(getDomain(indexA, true)), '<=', domain__debug(getDomain(indexB, true)));
        ml_enc8(ml, currentOffset, ML_LTE);
        ml_enc16(ml, currentOffset + 1, 2);
        ml_enc16(ml, currentOffset + OFFSET_C_A, indexA);
        ml_enc16(ml, currentOffset + OFFSET_C_B, indexB);
        ++i;
        size -= SIZEOF_C_2;
        currentOffset += SIZEOF_C_2;
      } while (size >= SIZEOF_C_2 && i < toRecycle);

      if (size) ml_compileJumpSafe(ml, currentOffset, size);

      if (process.env.NODE_ENV !== 'production') {
        ml_validateSkeleton(ml); // Cant check earlier
      }
    }

    return true;
  }

  function trick_imprhs_isall_entry(indexS, impOffset, countsS, indexA) {
    // A -> S, S = all?(B C...)    =>    A -> B, A -> C
    var offset1 = bounty_getOffset(bounty, indexS, 0);
    var offset2 = bounty_getOffset(bounty, indexS, 1);
    TRACE('trick_imprhs_isall_entry; ', indexS, 'at', impOffset, '=>', offset1, offset2, '`; A -> S, S = all?(B C...)    =>    A -> B, A -> C`');
    ASSERT(impOffset === offset1 || impOffset === offset2, 'expecting current offset to be one of the two offsets found', impOffset, indexS);
    var isallOffset = impOffset === offset1 ? offset2 : offset1; // This stuff should have been checked by the bounty hunter, so we tuck them in ASSERTs

    ASSERT(ml_dec8(ml, impOffset) === ML_IMP, 'impOffset should be an imp');
    ASSERT(ml_dec8(ml, isallOffset) === ML_ISALL, 'isall offset should be either isall op');
    ASSERT(getMeta(bounty, indexS) === (BOUNTY_FLAG_IMP_RHS | BOUNTY_FLAG_ISALL_RESULT), 'kind of redundant, but this is what bounty should have yielded for this var');
    ASSERT(countsS === 2, 'S should only appear in two constraints');
    ASSERT((ml_dec8(ml, isallOffset) === ML_ISALL ? readIndex(ml, isallOffset + SIZEOF_C + ml_dec16(ml, isallOffset + 1) * 2) : readIndex(ml, isallOffset + 5)) === indexS, 'S should the result of the isall');
    ASSERT(readIndex(ml, impOffset + OFFSET_C_A) === indexA, 'A should be lhs of IMP'); // We can replace an isall and IMP with IMPs on the args of the isall
    // A -> S, S = isall(C D)    =>     A -> C, A -> D
    // note that A must be strict bool and A must have a 0 for this to be safe. S is our shared var here.
    // [01] -> [01], [01] = isall(....)
    // if you dont apply this condition:
    // [0 0 5 5 9 9] -> [0 0 9 9], [0 0 9 9] = isall([55], [66])
    // after the morph A _must_ be 0 or 5 while before it could also be 9.

    var A = getDomain(indexA, true);
    ASSERT(indexS === readIndex(ml, impOffset + OFFSET_C_B), 'S should be rhs of IMP');
    var S = getDomain(indexS, true); // Mostly A will be [01] but dont rule out valid cases when A=0 or A=1

    if (domain_max(A) > 1 && domain_max(S) > 1) {
      TRACE(' - neither A nor S was boolean bound, bailing', domain__debug(A), domain__debug(S));
      return false;
    }

    if (domain_hasNoZero(S)) {
      // (dead code because minifier should eliminate an isall when R>=1)
      TRACE('- S has no zero which it would need to reflect any solution as a leaf, bailing', domain__debug(S)); // (unless the isall was already solved, but the minimizer should take care of that)

      requestAnotherCycle = true;
      return false;
    }

    if (domain_max(A) > domain_max(S)) {
      // (dead code because minifier should eliminate an isall when R=0)
      TRACE(' - max(A) > max(S) so there is a value in A that S couldnt satisfy A->S so we must bail', domain__debug(A), domain__debug(S)); // We can only trick if S can represent any valuation of A and there is a reject possible so no
      // note that this shouldnt happen when the minimizer runs to the max, but could in single cycle mode

      requestAnotherCycle = true;
      return false;
    }

    TRACE(' - A and S are okay proceeding with morph, ', domain__debug(A), '->', domain__debug(S));
    ASSERT(ml_dec8(ml, isallOffset) === ML_ISALL, 'bounty should have asserted this');
    var argCount = ml_dec16(ml, isallOffset + 1);
    TRACE(' - an isall starting at', isallOffset, 'and has', argCount, 'args; rewriting A -> S, S=isall(X Y Z ...)  =>  A -> X, A -> Y, A -> Z, ...');

    if (argCount < 2) {
      TRACE(' - argcount < 2, so a bug or an alias. ignoring that here. bailing');
      requestAnotherCycle = true; // Minifier should tear this down

      return false;
    } // First encode the isall args beyond the second one (if any) into recycled spaces


    if (argCount > 2) {
      var proceed = trick_imprhs_isall_entry_excess(ml, isallOffset, argCount, indexA);
      if (!proceed) return false;
    } // Now morph the first two args into the existing IMP and isall (of same size)


    var indexX = readIndex(ml, isallOffset + OFFSET_C_A);
    var indexY = readIndex(ml, isallOffset + OFFSET_C_B);
    TRACE(' -  A -> S, S=isall(X Y, ...(already done the rest))   =>    A -> X, A -> Y'); // Must mark all affected vars. their bounty data is probably obsolete now.
    // (collect the isall before morphing it!)

    bounty_markVar(bounty, indexA);
    bounty_markVar(bounty, indexS);
    var isallArgs = markAndCollectArgs(ml, isallOffset, argCount);
    ASSERT(isallArgs[0] === indexX, 'x should be collected');
    ASSERT(isallArgs[1] === indexY, 'y should be collected');
    TRACE(' - isall args:', isallArgs, ', and from the IMP A=', indexA, ', S=', indexS); // Compile A->left and A->right over the existing two offsets

    ml_c2c2(ml, impOffset, 2, ML_IMP, indexA, indexX);
    ml_cr2c2(ml, isallOffset, argCount, ML_IMP, indexA, indexY);
    TRACE('   - deferring', indexS, 'will be gt', indexA, 'and the result of an isall');
    solveStack.push(function (_, force, getDomain, setDomain) {
      // Note: we cut out indexS so that's what we restore here!
      TRACE(' - trick_imprhs_isall_entry; patching index', indexS);
      TRACE('   -', indexA, '->', indexS, '  =>  ', domain__debug(getDomain(indexA)), '->', domain__debug(getDomain(indexS)));
      TRACE('   -', indexS, '= all?(', isallArgs, ')  =>  ', domain__debug(getDomain(indexS)), '= all?(', isallArgs.map(function (index) {
        return domain__debug(getDomain(index));
      }), ')');
      var S = getDomain(indexS);
      var A = getDomain(indexA);
      TRACE(' - must first scan whether S ought to be set or unset according to the other imp/isall args'); // Check whether S is forced at all by the imp or isall

      var isSet = false;
      var isUnset = false;
      TRACE(' - A->S so if A is set, S must be set; A>0?', domain_hasNoZero(A));

      if (domain_hasNoZero(A)) {
        TRACE(' - A is set so S must be set');
        isSet = true;
      }

      TRACE(' - check the "set" state of all args');
      var allSet = true;

      for (var i = 0; i < argCount; ++i) {
        var index = isallArgs[i];
        var D = getDomain(index);
        TRACE('    - index:', index, ', D:', domain__debug(D));

        if (domain_isZero(D)) {
          TRACE('    - isall had an arg that was zero so S must be zero');
          isUnset = true;
          allSet = false;
          break;
        } else if (domain_hasZero(D)) {
          TRACE('    - isall had at least one arg that wasnt set yet so the isall does not force S to be set, at least');
          allSet = false;
        }
      }

      if (allSet) {
        TRACE(' - all args of the isall were set so S must be set');
        isSet = true;
      }

      TRACE(' - result of scan: set?', isSet, ', unset?', isUnset);
      ASSERT(!(isSet && isUnset), 'shouldnt be both set and unset');
      var result = false;

      if (isSet) {
        setDomain(indexS, domain_removeValue(S, 0));
        result = true;
      } else if (isUnset) {
        setDomain(indexS, domain_removeGtUnsafe(S, 0));
        result = false;
      } else {
        result = force(indexS) > 0;
        TRACE(' - forced S to', result);
      }

      TRACE(' - now apply the state of S=', result ? 1 : 0, ' to the other args');
      TRACE('   -', domain__debug(getDomain(indexA)), '->', result ? 1 : 0);
      TRACE('   -', result ? 1 : 0, '= all?(', isallArgs.map(function (index) {
        return domain__debug(getDomain(index));
      }), ')'); // A -> S so if S=0 then A=0

      if (!result) {
        TRACE(' - A->S, S=0 so A=0');
        setDomain(indexA, domain_removeGtUnsafe(A, 0));
      }

      var found = false;

      for (var _i5 = 0; _i5 < argCount; ++_i5) {
        var _index3 = isallArgs[_i5];

        var _D3 = getDomain(_index3);

        if (result) {
          // True=isall(...D) so D>0
          TRACE(' - S>0 so all args must be >0');
          setDomain(_index3, domain_removeValue(_D3, 0));
        } else if (domain_isZero(_D3)) {
          found = true;
          break;
        } else if (domain_hasZero(_D3)) {
          // False=isall(...D) so D=0
          TRACE(' - S=0 so one arg must be 0');
          setDomain(_index3, domain_removeGtUnsafe(_D3, 0));
          found = true;
          break;
        }
      }

      TRACE(' - final result:');
      TRACE('   -', domain__debug(getDomain(indexA)), '->', result ? 1 : 0);
      TRACE('   -', result ? 1 : 0, '= all?(', isallArgs.map(function (index) {
        return domain__debug(getDomain(index));
      }), ')');
      ASSERT(getDomain(indexA));
      ASSERT(getDomain(indexS));
      ASSERT(!isallArgs.some(function (index) {
        return !getDomain(index);
      }));
      ASSERT(domain_hasNoZero(getDomain(indexA)) ? domain_hasNoZero(getDomain(indexS)) : 1);
      ASSERT(domain_isZero(getDomain(indexS)) ? domain_isZero(getDomain(indexA)) : 1);
      ASSERT(domain_isSolved(getDomain(indexS)));
      ASSERT(domain_isZero(getDomain(indexS)) === isallArgs.some(function (index) {
        return domain_isZero(getDomain(index));
      }));
      ASSERT(result || found, 'if result is false at least one arg should be false');
    });
    somethingChanged();
    return true;
  }

  function trick_imprhs_isall_entry_excess(ml, isallOffset, argCount, indexA) {
    // Isall has four or more args
    // A -> S, S=isall(X Y Z ...)  =>  A -> X, A -> Y, A -> Z, ...
    // note: this function only compiles the args from Z (the third isall arg) onward
    TRACE(' - trick_imprhs_isall_entry_excess. Attempting to recycle space to stuff', argCount - 2, 'IMP constraints');
    ASSERT(argCount > 2, 'this function should only be called for 3+ isall args'); // We have to recycle some space now. we wont know whether we can
    // actually do the morph until we've collected enough space for it.
    // we'll use impOffset and isallOffset to compile the last 2 args so only need space for the remaining ones

    var toRecycle = argCount - 2; // Start by collecting toRecycle recycled spaces

    var bins = ml_getRecycleOffsets(ml, 0, toRecycle, SIZEOF_C_2);

    if (!bins) {
      TRACE(' - Was unable to find enough free space to fit', argCount, 'IMPs, bailing');
      return false;
    }

    TRACE(' - Found', bins.length, 'jumps (', bins, ') which can host (at least)', toRecycle, 'IMP constraints. Compiling them now'); // Okay, now we'll morph. be careful about clobbering existing indexes... start with
    // last address to make sure jumps dont clobber existing jump offsets in the bin

    var i = 0;

    while (i < toRecycle) {
      var currentOffset = bins.pop();
      ASSERT(ml_dec8(ml, currentOffset) === ML_JMP, 'should only get jumps here'); // Might trap a case where we clobber

      var size = ml_getOpSizeSlow(ml, currentOffset);
      ASSERT(size >= SIZEOF_C_2, 'this is what we asked for');

      do {
        var indexB = readIndex(ml, isallOffset + SIZEOF_C + (i + 2) * 2); // Note: i+2 because we skip the first two args. they are done by caller

        TRACE('  - compiling IMP:', indexA, '->', indexB, ' -> ', domain__debug(getDomain(indexA, true)), '->', domain__debug(getDomain(indexB, true)));
        ml_enc8(ml, currentOffset, ML_IMP);
        ml_enc16(ml, currentOffset + 1, 2);
        ml_enc16(ml, currentOffset + OFFSET_C_A, indexA);
        ml_enc16(ml, currentOffset + OFFSET_C_B, indexB);
        ++i;
        size -= SIZEOF_C_2;
        currentOffset += SIZEOF_C_2;
      } while (size >= SIZEOF_C_2 && i < toRecycle);

      if (size) ml_compileJumpSafe(ml, currentOffset, size);

      if (process.env.NODE_ENV !== 'production') {
        ml_validateSkeleton(ml); // Cant check earlier
      }
    }

    return true;
  }

  function trick_issame_lterhs(indexR, lteOffset, countsR, indexC) {
    TRACE('trick_issame_lterhs');
    TRACE('   - R = A ==? B, C <= R    =>       R = A ==? B, C -> R');
    TRACE('   - (if the requirements hold it only morphs an lte to an imp)');
    ASSERT(countsR === 2, 'should be leaf var'); // Prerequisites: all bools, R leaf (the latter has been confirmed)

    var offset1 = bounty_getOffset(bounty, indexR, 0);
    var offset2 = bounty_getOffset(bounty, indexR, 1);
    var issameOffset = offset1 === lteOffset ? offset2 : offset1;
    ASSERT(ml_dec8(ml, issameOffset) === ML_ISSAME, 'should be issame');
    ASSERT(readIndex(ml, issameOffset + OFFSET_C_R) === indexR, 'issame result should be R');

    if (ml_dec16(ml, issameOffset + 1) !== 2) {
      TRACE(' - isall does not have 2 args, bailing');
      return false;
    }

    var indexA = readIndex(ml, issameOffset + OFFSET_C_A);
    var indexB = readIndex(ml, issameOffset + OFFSET_C_B);
    var A = getDomain(indexA, true);
    var B = getDomain(indexB, true);
    var C = getDomain(indexC, true);
    var R = getDomain(indexR, true);
    TRACE(' - domains; A=', domain__debug(A), ', B=', domain__debug(B), ', C=', domain__debug(C), ', R=', domain__debug(R));

    if (!domain_isBool(A) || !domain_isBool(B) || !domain_isBool(C) || !domain_isBool(R)) {
      TRACE(' - at least one of the three domains isnt bool, bailing');
      return false;
    } // Okay. morph the lte into implication


    TRACE(' - morphing, R = A ==? B, C <= R      =>       R = A ==? B, C -> R');
    ml_c2c2(ml, lteOffset, 2, ML_IMP, indexC, indexR); // Dont mark A or B because we did not change their ops

    bounty_markVar(bounty, indexC);
    bounty_markVar(bounty, indexR);
    somethingChanged();
    return true;
  }

  function trick_isall_nall_2shared(ml, indexR, isallOffset, counts) {
    // R = all?(A B), nall(R A D)   ->    R = all?(A B), R !& D
    var offset1 = bounty_getOffset(bounty, indexR, 0);
    var offset2 = bounty_getOffset(bounty, indexR, 1);
    TRACE('trick_isall_nall_2shared', indexR, 'at', isallOffset, 'and', offset1, '/', offset2, 'metaFlags:', getMeta(bounty, indexR, true), '`R = all?(A B), nall(R A D)`   ->    `R = all?(A B), R !& D`');
    var nallOffset = offset1 === isallOffset ? offset2 : offset1;
    var argCountNall = ml_dec16(ml, nallOffset + 1);
    var argCountIsall = ml_dec16(ml, isallOffset + 1); // This stuff should have been checked by the bounty hunter, so we tuck them in ASSERTs

    ASSERT(getMeta(bounty, indexR) === (BOUNTY_FLAG_NALL | BOUNTY_FLAG_ISALL_RESULT), 'the var should only be part of a nall and the result of an isall');
    ASSERT(counts === 2, 'R should only appear in two constraints');
    ASSERT(isallOffset === offset1 || isallOffset === offset2, 'expecting current offset to be one of the two offsets found', isallOffset, indexR);
    ASSERT(ml_dec8(ml, isallOffset) === ML_ISALL, 'isall offset should be an isall');
    ASSERT(ml_dec8(ml, nallOffset) === ML_NALL, 'other offset should be a nall');
    ASSERT(getAlias(indexR) === indexR, 'should be unaliased');
    ASSERT(readIndex(ml, isallOffset + SIZEOF_C + argCountIsall * 2) === indexR, 'var should be R of isall'); // This should be `R = all?(A B ...), nall(R A D)`
    // if R = 1 then A and B (etc) are 1, so the nall will have two 1's, meaning D must be 0
    // if R = 0 then the nall is already satisfied. neither the nall nor the isall is redundant
    // because `R !& D` must be maintained, so remove the shared arg from the nall

    if (argCountNall !== 3) {
      TRACE(' - fingerprint didnt match (', argCountNall, ' !== 3) so bailing');
      return false;
    } // (this is kind of dead code since isall1 wont get 2 args and that's required for this trick)


    TRACE(' - nall has 3 args, check if it shares an arg with the isall'); // Next; one of the two isalls must occur in the nall
    // R = all?(A B), nall(R A C)
    // R = all?(A B), nall(X Y Z)
    // nall args

    var indexX = readIndex(ml, nallOffset + SIZEOF_C);
    var indexY = readIndex(ml, nallOffset + SIZEOF_C + 2);
    var indexZ = readIndex(ml, nallOffset + SIZEOF_C + 4);
    TRACE(' - nall(' + [indexX, indexY, indexZ] + ') -> nall(', [domain__debug(getDomain(indexX, true)), domain__debug(getDomain(indexY)), domain__debug(getDomain(indexZ))], ')');

    for (var i = 0; i < argCountIsall; ++i) {
      var argIndex = readIndex(ml, isallOffset + SIZEOF_C + i * 2);
      if (argIndex === indexX) return _updateNallForTrick(ml, nallOffset, indexY, indexZ, indexX);
      if (argIndex === indexY) return _updateNallForTrick(ml, nallOffset, indexX, indexZ, indexY);
      if (argIndex === indexZ) return _updateNallForTrick(ml, nallOffset, indexX, indexY, indexZ);
    }

    TRACE(' - no shared args');
    return false;
  }

  function _updateNallForTrick(ml, offset, indexA, indexB, indexDropped) {
    TRACE(' - isall arg matches an arg of nall. dropping it from the nall'); // Since we know the nall has 3 args we can simply write the two args we want and a noop for the last position
    // keep A and B, the other index is dropped because we're writing a noop in its place

    ASSERT(ml_dec8(ml, offset) === ML_NALL, 'should be nall');
    ASSERT(ml_dec16(ml, offset + 1) === 3, 'nall should have 3 args');
    ml_enc16(ml, offset + 1, 2); // Down from 3 to 2 args

    ml_enc16(ml, offset + OFFSET_C_A, indexA);
    ml_enc16(ml, offset + OFFSET_C_B, indexB);
    ml_enc8(ml, offset + OFFSET_C_C, ML_NOOP2); // This only affected the nall and its args so no need to mark the isall vars

    bounty_markVar(bounty, indexDropped);
    bounty_markVar(bounty, indexA);
    bounty_markVar(bounty, indexB);
    somethingChanged();
    return true;
  }

  function trick_ltelhs_nall_leaf(ml, indexA, countsA) {
    // A <= B, A !& C   ->   A leaf, all constraints dropped. for _any_ lte_lhs / nall
    TRACE('trick_ltelhs_nall_leaf; bounty A:', bounty__debug(bounty, indexA));
    TRACE(' - indexA=', indexA, '; `A <= B, A !& C   ->   nothing (for any number of LTE_LHS and NAND ops).');
    TRACE('   - A=', domain__debug(getDomain(indexA)), '; if it has a zero it can never break LTE_LHS or NALL'); // Rationale; assuming A has at least a zero, there's no valuation of B or C that could lead to breaking
    // the <= or !& constraints. so A can still be considered a leaf var.
    // note that the number of args of the NALL is irrelevant

    ASSERT(getMeta(bounty, indexA) === BOUNTY_FLAG_LTE_LHS || getMeta(bounty, indexA) === BOUNTY_FLAG_NALL || getMeta(bounty, indexA) === (BOUNTY_FLAG_NALL | BOUNTY_FLAG_LTE_LHS), 'the var should only be lhs of LTEs or part of NALLs');
    ASSERT(getAlias(indexA) === indexA, 'should be unaliased'); // TODO: what if there aren't any NALLs? then A could still be a leaf even if it was nonzero
    // A must contain zero for this to work for else it may not solve the nall

    if (domain_hasNoZero(getDomain(indexA, true))) {
      TRACE(' - A contains no zero, bailing');
      return false;
    } // No need for further verification.


    TRACE(' - marking LTE/NALL args, eliminating the constraints');

    for (var i = 0; i < countsA; ++i) {
      var offset = bounty_getOffset(bounty, indexA, i);
      var opCode = ml_dec8(ml, offset);
      TRACE('    - next op:', ml__debug(ml, offset, 1, problem));

      if (opCode === ML_LTE) {
        ASSERT(readIndex(ml, offset + OFFSET_C_A) === indexA, 'A should (at least) be LTE_LHS');
        ASSERT(readIndex(ml, offset + 1) === 2, 'LTE is assumed to always have 2 args');
        var index = readIndex(ml, offset + OFFSET_C_B);

        if (index !== indexA) {
          bounty_markVar(bounty, index);
          ml_eliminate(ml, offset, SIZEOF_C_2);
        }
      } else if (opCode === ML_NALL) {
        var argCount = readIndex(ml, offset + 1);

        for (var j = 0; j < argCount; ++j) {
          var _index4 = readIndex(ml, offset + SIZEOF_C + j * 2);

          if (_index4 !== indexA) {
            bounty_markVar(bounty, _index4);
          }
        }

        ml_eliminate(ml, offset, SIZEOF_C + argCount * 2);
      } else {
        ASSERT(false, 'bounty should have asserted A to only be LTE_LHS and NALL so this cant happen?');
        TRACE(' - the unthinkable happened, bailing'); // *Shrug* it's not a problem to throw for

        return false;
      }
    } // Note: We could go through great lengths in an effort to reduce A as little as possible but since
    // this trick involves any number of NALLs and LTEs, this leads to a bunch of difficult checks and
    // heuristics. And even then we're still very likely to set A to zero anyways.
    // Let's save us the code head ache here and just do it now.


    TRACE(' - setting A to zero for the sake of simplicity');
    var A = getDomain(indexA, true);
    var nA = domain_removeGtUnsafe(A, 0);
    if (A !== nA) setDomain(indexA, nA);
    bounty_markVar(bounty, indexA);
    somethingChanged();
    return true;
  }

  function trick_implhs_nall_leaf(ml, indexA, countsA) {
    // For all A, A -> B, A !& C   =>   cut A, all constraints dropped. for _any_ imp_lhs / nall on A
    TRACE('trick_implhs_nall_leaf');
    TRACE(' - indexA=', indexA, ', bounty A:', bounty__debug(bounty, indexA));
    TRACE_MORPH('A -> B, A !& C', '', '(for any number of IMP_LHS and NAND ops).');
    TRACE('   - A=', domain__debug(getDomain(indexA)), '; if it has a zero it can never break IMP_LHS or NALL'); // Rationale; assuming A has at least a zero, there's no valuation of B or C that could lead to breaking
    // the -> or !& constraints. so A can still be considered a leaf var.
    // note that the number of args of the NALL is irrelevant

    ASSERT(getMeta(bounty, indexA) === BOUNTY_FLAG_IMP_LHS || getMeta(bounty, indexA) === BOUNTY_FLAG_NALL || getMeta(bounty, indexA) === (BOUNTY_FLAG_NALL | BOUNTY_FLAG_IMP_LHS), 'the var should only be lhs of IMPs or part of NALLs');
    ASSERT(getAlias(indexA) === indexA, 'should be unaliased'); // TODO: what if there aren't any NALLs? then A could still be a leaf even if it was nonzero
    // A must contain zero for this to work for else A may not solve the nall

    if (domain_hasNoZero(getDomain(indexA, true))) {
      TRACE(' - A contains no zero, bailing');
      requestAnotherCycle = true;
      return false;
    } // No need for further verification.
    // A is only the IMP_LHS or NALL arg
    // if we set it to 0 here then those immediately solve
    // we could go into great code complexity here handling everything nicely
    // or we could just set it to 0 here and request another run. oh yes.


    TRACE_MORPH('A -> B, A !& C', 'A=0', 'this will solve all implications and nalls');
    TRACE(' - setting A to zero for the sake of simplicity');
    var A = getDomain(indexA, true);

    if (!domain_isZero(A)) {
      var nA = domain_removeGtUnsafe(A, 0);
      if (A !== nA) setDomain(indexA, nA);
      bounty_markVar(bounty, indexA);
    }

    somethingChanged(); // This will require another minimizer as well

    return true;
  }

  function trick_ltelhs_some_leaf(ml, lteOffset, indexA, countsA) {
    // A <= B, A | C   =>   B | C, A leaf
    TRACE('trick_ltelhs_some_leaf');
    TRACE(' - A <= B, some(A C ...)     =>     some(B C ...), A leaf');
    var A = getDomain(indexA, true);
    TRACE(' - indexA=', indexA, ', =', domain__debug(A));
    ASSERT(getMeta(bounty, indexA) === (BOUNTY_FLAG_LTE_LHS | BOUNTY_FLAG_SOME), 'A is leaf on an LTE and SOME');
    ASSERT(getAlias(indexA) === indexA, 'should be unaliased');
    ASSERT(countsA === 2, 'should have 2 offsets');

    if (!domain_isBool(A)) {
      TRACE(' - A wasnt a bool, bailing');
      return false;
    }

    var indexB = readIndex(ml, lteOffset + OFFSET_C_B);
    var B = getDomain(indexB, true);

    if (!domain_isBool(B)) {
      TRACE(' - B wasnt a bool, bailing');
      return false;
    }

    TRACE(' - constraints verified, applying trick');
    TRACE_MORPH('A <= B, some(A C ...)', 'some(B C ...)', 'A is leaf');
    var offset1 = bounty_getOffset(bounty, indexA, 0);
    var offset2 = bounty_getOffset(bounty, indexA, 1);
    var someOffset = offset1 === lteOffset ? offset2 : offset1;
    ASSERT(ml_dec8(ml, someOffset) === ML_SOME); // Note: arg count of the SOME is not important. A must simply be part of it (and bounty asserted that already)

    var argCount = ml_dec16(ml, someOffset + 1);
    var args = markAndCollectArgs(ml, someOffset, argCount, indexA);
    ml_eliminate(ml, lteOffset, SIZEOF_C_2);
    ml_cx2cx(ml, someOffset, argCount, ML_SOME, [indexB].concat(args));
    solveStack.push(function (_, force, getDomain, setDomain) {
      TRACE(' - trick_ltelhs_some_leaf');
      TRACE(' - A <= B, some(A C ...)    =>     some(B C ...)');
      var A = getDomain(indexA);
      var B = getDomain(indexB);
      var nA = A; // Ensure A<=B

      if (domain_max(nA) > domain_min(B)) {
        nA = domain_removeGtUnsafe(nA, domain_min(B));
      } // Ensure the SOME holds


      if (!domain_isZero(nA)) {
        var removeZero = true; // Without other args, A must be nonzero to satisfy the SOME

        for (var i = 0, len = args.length; i < len; ++i) {
          var index = args[i];
          var D = getDomain(index);

          if (domain_hasNoZero(D)) {
            // At least one arg already satisfies the SOME
            break;
          }

          if (domain_isBooly(D)) {
            removeZero = true; // At least one arg is undetermined so to make sure its value is irrelevant we set A>0

            break;
          }

          removeZero = false;
        }

        if (removeZero) {
          nA = domain_removeValue(nA, 0);
        }
      }

      ASSERT(nA, 'A should hold all values');
      if (A !== nA) setDomain(indexA, nA);
    });
    bounty_markVar(bounty, indexA);
    somethingChanged();
    return true;
  }

  function trick_implhs_some_leaf(ml, impOffset, indexA, countsA) {
    // A -> B, A | C   =>   B | C, A leaf
    TRACE('trick_implhs_some_leaf');
    TRACE(' - A -> B, some(A C ...)     =>     some(B C ...), A leaf');
    var A = getDomain(indexA, true);
    TRACE(' - indexA=', indexA, ', =', domain__debug(A));
    ASSERT(getMeta(bounty, indexA) === (BOUNTY_FLAG_IMP_LHS | BOUNTY_FLAG_SOME), 'A is leaf on an IMP and SOME');
    ASSERT(getAlias(indexA) === indexA, 'should be unaliased');
    ASSERT(countsA === 2, 'should have 2 offsets');

    if (!domain_isBool(A)) {
      TRACE(' - A wasnt a bool, bailing');
      return false;
    }

    var indexB = readIndex(ml, impOffset + OFFSET_C_B);
    var B = getDomain(indexB, true);

    if (!domain_isBool(B)) {
      TRACE(' - B wasnt a bool, bailing');
      return false;
    }

    TRACE(' - constraints verified, applying trick');
    TRACE_MORPH('A -> B, some(A C ...)', 'some(B C ...)', 'A is leaf');
    var offset1 = bounty_getOffset(bounty, indexA, 0);
    var offset2 = bounty_getOffset(bounty, indexA, 1);
    var someOffset = offset1 === impOffset ? offset2 : offset1;
    ASSERT(ml_dec8(ml, someOffset) === ML_SOME); // Note: arg count of the SOME is not important. A must simply be part of it (and bounty asserted that already)

    var argCount = ml_dec16(ml, someOffset + 1);
    var args = markAndCollectArgs(ml, someOffset, argCount, indexA);
    ml_eliminate(ml, impOffset, SIZEOF_C_2);
    ml_cx2cx(ml, someOffset, argCount, ML_SOME, [indexB].concat(args));
    solveStack.push(function (_, force, getDomain, setDomain) {
      TRACE(' - trick_implhs_some_leaf');
      TRACE(' - A -> B, some(A C ...)    =>     some(B C ...)');
      var A = getDomain(indexA);
      var B = getDomain(indexB);
      var nA = A; // Ensure A->B

      if (domain_hasNoZero(B)) {
        nA = domain_removeValue(nA, 0);
      } else {
        nA = domain_removeGtUnsafe(nA, 0);
      } // Ensure the SOME holds


      if (!domain_isZero(nA)) {
        var removeZero = true; // Without other args, A must be nonzero to satisfy the SOME

        for (var i = 0, len = args.length; i < len; ++i) {
          var index = args[i];
          var D = getDomain(index);

          if (domain_hasNoZero(D)) {
            // At least one arg already satisfies the SOME
            break;
          }

          if (domain_isBooly(D)) {
            removeZero = true; // At least one arg is undetermined so to make sure its value is irrelevant we set A>0

            break;
          }

          removeZero = false;
        }

        if (removeZero) {
          nA = domain_removeValue(nA, 0);
        }
      }

      ASSERT(nA, 'A should hold all values');
      if (A !== nA) setDomain(indexA, nA);
    });
    bounty_markVar(bounty, indexA);
    somethingChanged();
    return true;
  }

  function trick_imp_islte_c_v(islteOffset, indexR, indexA, indexB, countsR) {
    TRACE('trick_imp_islte_c_v');
    TRACE(' - R = A <=? B, B -> R, solved(A)  =>  R = A <=? B'); // First search for the imp offset

    for (var i = 0; i < countsR; ++i) {
      var offset = bounty_getOffset(bounty, indexR, i);

      if (offset !== islteOffset) {
        var op = ml_dec8(ml, offset);

        if (op === ML_IMP) {
          if (readIndex(ml, offset + OFFSET_C_A) === indexB && readIndex(ml, offset + OFFSET_C_B) === indexR) {
            return _trick_imp_islte_c_v(indexR, indexA, indexB, islteOffset, offset);
          }
        }
      }
    }

    ASSERT(false, 'bounty should have asserted this imp exists');
    return false;
  }

  function _trick_imp_islte_c_v(indexR, indexA, indexB, islteOffset, impOffset) {
    TRACE(' - _trick_imp_islte_c_v; R = A <=? B, B -> R   =>   R !^ B, remove [1..A-1] from B');
    ASSERT(domain_isSolved(getDomain(indexA))); // Note:
    // - if R=0 then B->R then B->0 then 0->0 so B=0
    // - if R>0 then B->R always holds and R=vA<=?B holds when B>=vA
    // - if vA<=min(B) then R>0 because vA cannot be >B
    // - if vA>max(B) then R=0 because vA cannot be <=B
    // so R !^ B and remove from B all values from 1 up to but not including vA
    // [01] = 2 <=? [02], [02] -> [01]
    // R=0
    // => 0 = 2 <=? [02], [02] -> 0
    // => 2 > [02], [02] -> 0
    // => 2 > 0, 0 -> 0
    // R>0
    // => 1 = 2 <=? [02], [02] -> 1
    // => 2 <= [02], [02] -> 1
    // => 2 <= 2, 2 -> 1
    // [01] = 5 <=? [09], [09] -> [01]
    // R=0
    // => 0 = 2 <=? [09], [09] -> 0
    // => 2 > [09], [09] -> 0
    // => 2 > [01], [01] -> 0
    // => 2 > 0, 0 -> 0
    // R>0
    // => 1 = 2 <=? [09], [09] -> 1
    // => 2 <= [09], [09] -> 1
    // => 2 <= [29], [29] -> 1

    var A = getDomain(indexA, true);
    var B = getDomain(indexB, true);
    var vA = domain_getValue(A);
    TRACE(' - first checking;', vA, '<=', domain_min(B), ' and ', vA, '>', domain_max(B));

    if (vA <= domain_min(B)) {
      // R>0 because if R=0 then A>B and that's not possible
      // let minimizer take this down
      TRACE(' - A<=min(B) means R>0, minimizer can solve this, bailing');
      requestAnotherCycle = true;
      return false;
    }

    if (vA > domain_max(B)) {
      TRACE(' - A > max(B), minimizer can solve this, bailing');
      requestAnotherCycle = true;
      return false;
    }

    TRACE_MORPH('R = A <=? B, B -> R', 'R !^ B, remove [1..A-1] from B');
    TRACE(' - indexes: A=', indexA, ', B=', indexB, ', R=', indexR);
    TRACE(' - domains: A=', domain__debug(getDomain(indexA)), ', B=', domain__debug(getDomain(indexB)), ', R=', domain__debug(getDomain(indexR))); // Create a mask that removes 1..A then intersect B with that mask (because B may already be missing more values)

    var mask = domain_arrToSmallest([0, 0, vA, domain_max(B)]);
    var nB = domain_intersection(B, mask);
    TRACE(' - B mask:', domain__debug(mask), ', B after mask:', domain__debug(mask)); // Probably the same

    if (B !== nB) {
      setDomain(indexB, nB);
      if (!nB) return emptyDomain = true;
    }

    ml_c2c2(ml, impOffset, 2, ML_XNOR, indexR, indexB);
    ml_eliminate(ml, islteOffset, SIZEOF_VVV);
    bounty_markVar(bounty, indexB);
    bounty_markVar(bounty, indexR);
    somethingChanged();
    return true;
  }

  function trick_imp_islte_v_c(islteOffset, indexR, indexA, indexB, countsR) {
    TRACE('trick_imp_islte_c_v');
    TRACE(' - R = A <=? B, A -> R, solved(B)  =>  R > 0, A <= B'); // First search for the imp offset

    for (var i = 0; i < countsR; ++i) {
      var offset = bounty_getOffset(bounty, indexR, i);

      if (offset !== islteOffset) {
        var op = ml_dec8(ml, offset);

        if (op === ML_IMP) {
          if (readIndex(ml, offset + OFFSET_C_A) === indexA && readIndex(ml, offset + OFFSET_C_B) === indexR) {
            return _trick_imp_islte_v_c(indexR, indexA, indexB, islteOffset, offset);
          }
        }
      }
    }

    ASSERT(false, 'bounty should have asserted this imp exists');
    return false;
  }

  function _trick_imp_islte_v_c(indexR, indexA, indexB, islteOffset, impOffset) {
    TRACE(' - _trick_imp_islte_c_v');
    ASSERT(domain_isSolved(getDomain(indexB))); // Note:
    // - if R=0 then A > vB then A>0 then A->R so R>0 then falsum
    // - if R>0 then A <= vB then A->R always holds because R>0
    // - so R>0, islte becomes lte, imp is eliminated

    var R = getDomain(indexR, true);
    R = domain_removeValue(R, 0);

    if (!R) {
      emptyDomain = true;
      return false;
    }

    var A = getDomain(indexA, true);
    var B = getDomain(indexB, true);

    if (domain_getValue(B) <= domain_min(A)) {
      TRACE(' - B <= min(A), minimizer can solve this, bailing');
      requestAnotherCycle = true;
      return false;
    }

    TRACE_MORPH('R = A <=? B, A -> R', 'R > 0, A <= B');
    TRACE(' - indexes: A=', indexA, ', B=', indexB, ', R=', indexR);
    TRACE(' - domains: A=', domain__debug(getDomain(indexA)), ', B=', domain__debug(getDomain(indexB)), ', R=', domain__debug(getDomain(indexR)));
    setDomain(indexR, R);
    ml_c2c2(ml, impOffset, 2, ML_LTE, indexA, indexB);
    ml_eliminate(ml, islteOffset, SIZEOF_VVV);
    bounty_markVar(bounty, indexA);
    bounty_markVar(bounty, indexB);
    bounty_markVar(bounty, indexR);
    somethingChanged();
    return true;
  }

  function trick_only_ltelhs_leaf(ml, indexA, countsA) {
    TRACE('trick_only_ltelhs_leaf; bounty A:', bounty__debug(bounty, indexA));
    TRACE(' - A should only be an LTE_LHS for any number of LTE ops. cut it as a leaf and eliminate constraints'); // There is no way A breaks any LTEs unless there's already an rhs var that is smaller than it
    // no need to check here. just go.

    var A = getDomain(indexA, true);
    var rhsArgs = [];

    for (var i = 0; i < countsA; ++i) {
      var offset = bounty_getOffset(bounty, indexA, i);
      TRACE('    - next op:', ml__debug(ml, offset, 1, problem));
      ASSERT(ml_dec8(ml, offset) === ML_LTE);
      ASSERT(ml_dec16(ml, offset + 1) === 2, 'all LTE have 2 args');
      ASSERT(readIndex(ml, offset + OFFSET_C_A) === indexA, 'A should be the lhs');
      var indexB = readIndex(ml, offset + OFFSET_C_B);

      if (domain_max(getDomain(indexB)) < domain_min(A)) {
        TRACE(' indexB=', indexB, 'and it is already smaller than A;', domain__debug(A), '>', domain__debug(getDomain(indexB)));
        TRACE(' constraint cant hold, empty domain, rejecting');
        setDomain(indexB, 0);
        return true; // "true" as in "something awful happened"
      }

      rhsArgs.push(indexB);
      ml_eliminate(ml, offset, SIZEOF_C_2);
    }

    TRACE(' - Adding solve stack entry');
    solveStack.push(function (_, force, getDomain, setDomain) {
      TRACE(' - trick_only_ltelhs_leaf; shaving A to pass all LTEs');
      var A = getDomain(indexA);
      var nA = A;

      for (var _i6 = 0, il = rhsArgs.length; _i6 < il; ++_i6) {
        var _indexB = rhsArgs[_i6];
        TRACE('   - removing everything >', domain_min(getDomain(_indexB)), 'from', domain__debug(nA));
        nA = domain_removeGtUnsafe(nA, domain_min(getDomain(_indexB)));
      }

      ASSERT(nA, 'A should be able to be <= all the index B args');
      if (A !== nA) setDomain(indexA, nA);
    });
    bounty_markVar(bounty, indexA);

    for (var _i7 = 0, il = rhsArgs.length; _i7 < il; ++_i7) {
      bounty_markVar(bounty, rhsArgs[_i7]);
    }

    somethingChanged();
    return true;
  }

  function trick_only_implhs_leaf(ml, indexA, countsA) {
    TRACE('trick_only_implhs_leaf; bounty A:', bounty__debug(bounty, indexA));
    TRACE(' - A should only be an IMP_LHS for any number of IMP ops. confirm none of the Bs are zero. then cut it as a leaf and eliminate constraints');
    var A = getDomain(indexA, true);

    if (domain_isZero(A) || domain_hasNoZero(A)) {
      TRACE(' - A is not a booly. implication is resolved, let minimizer take care of it, bailing');
      requestAnotherCycle = true; // Force minimizer to take care of this one

      return false;
    } // The only way A breaks any IMPs is if it has an rhs that is zero. so check that first.


    for (var i = 0; i < countsA; ++i) {
      var offset = bounty_getOffset(bounty, indexA, i);
      TRACE('    - next op:', ml__debug(ml, offset, 1, problem));
      ASSERT(ml_dec8(ml, offset) === ML_IMP);
      ASSERT(readIndex(ml, offset + OFFSET_C_A) === indexA, 'A should be the lhs');
      var indexB = readIndex(ml, offset + OFFSET_C_B);

      if (domain_isZero(indexB)) {
        TRACE(' - indexB=', indexB, 'and is already zero;', domain__debug(A), '->', domain__debug(getDomain(indexB)));
        TRACE(' - implication is resolved, let minimizer take care of it, bailing');
        requestAnotherCycle = true; // Force minimizer to take care of this one

        return false;
      }
    }

    TRACE_MORPH('A -> B, A -> C, ...', 'A==0', 'leaf A, they dont break implication now so the implication cant break A once the rhs solves');
    var rhsArgs = [];

    for (var _i8 = 0; _i8 < countsA; ++_i8) {
      var _offset = bounty_getOffset(bounty, indexA, _i8);

      var _indexB2 = readIndex(ml, _offset + OFFSET_C_B);

      rhsArgs.push(_indexB2);
      ml_eliminate(ml, _offset, SIZEOF_C_2);
    } // TODO: could potentially improve "force" choice here but A=0 is definitely the simplest play


    TRACE(' - forcing A to 0 since thats the most likely outcome anyways and the safest play here');
    var nA = domain_intersectionValue(A, 0);
    ASSERT(nA !== A, 'since A was confirmed to be a booly before it should be different now');
    ASSERT(nA, 'since A was a booly we should be able to set it to 0');
    setDomain(indexA, nA);
    bounty_markVar(bounty, indexA);

    for (var _i9 = 0, il = rhsArgs.length; _i9 < il; ++_i9) {
      bounty_markVar(bounty, rhsArgs[_i9]);
    }

    somethingChanged();
    return true;
  }

  function trick_isall_nall_1shared(ml, indexR, isallOffset, countsR) {
    // R = all?(A B ...), R !& C  ->  nall(A B ... C)
    // note: this works for any nalls on one isall
    TRACE('trick_isall_nall_1shared;', indexR, '`R = all?(A B), R !& C  ->  nall(A B C)` for any nall on one isall, any arg count for either'); // This stuff should have been checked by the bounty hunter, so we tuck them in ASSERTs

    ASSERT(getMeta(bounty, indexR) === (BOUNTY_FLAG_NALL | BOUNTY_FLAG_ISALL_RESULT), 'the var should only be nall[2] and isall', bounty__debugMeta(bounty, indexR), countsR);
    ASSERT(ml_dec8(ml, isallOffset) === ML_ISALL, 'isall offset should be an isall');
    ASSERT(getAlias(indexR) === indexR, 'should be unaliased');
    ASSERT(readIndex(ml, isallOffset + SIZEOF_C + ml_dec16(ml, isallOffset + 1) * 2) === indexR, 'R should be result of isall');
    ASSERT(countsR < BOUNTY_MAX_OFFSETS_TO_TRACK, 'counts should not exceed maxed tracked');
    var isallArgCount = ml_dec16(ml, isallOffset + 1);
    var isallSizeof = SIZEOF_C + isallArgCount * 2 + 2;
    var isallArgs = [];

    for (var i = 0; i < isallArgCount; ++i) {
      var index = readIndex(ml, isallOffset + SIZEOF_C + i * 2);
      isallArgs.push(index);
    }

    TRACE(' - trick_isall_nall_1shared; first confirming all other offsets are nalls with 2 args; isall arg count:', isallArgCount, ', isall args:', isallArgs);
    var nalls = 0;

    for (var _i10 = 0; _i10 < countsR; ++_i10) {
      var nallOffset = bounty_getOffset(bounty, indexR, _i10);
      ASSERT(nallOffset, 'there should be as many offsets as counts unless that exceeds the max and that has been checked already');

      if (nallOffset !== isallOffset) {
        var opcode = ml_dec8(ml, nallOffset);

        if (opcode !== ML_NALL) {
          TRACE(' - found at least one other isall, bailing');
          ASSERT(opcode === ML_ISALL, 'bounty should have asserted that the offsets can only be isall and nall');
          return false;
        }

        if (ml_dec16(ml, nallOffset + 1) !== 2) {
          TRACE(' - found a nall that did not have 2 args, bailing for now');
          return false;
        }

        ++nalls;
      }

      ASSERT(nallOffset === isallOffset || readIndex(ml, nallOffset + OFFSET_C_A) === indexR || readIndex(ml, nallOffset + OFFSET_C_B) === indexR, 'R should be part of the nall');
    } // Bounty asserted that all these nalls contain R, rewrite each such nall


    TRACE(' - trick_isall_nall_1shared; there are', nalls, 'nalls; for each nall: `X !& B, X = all?(C D)`   ->   `nall(B C D)`');
    TRACE(' - one nall will fit inside the isall but any others need recycled spaces (because the existing nalls have 2 args)'); // Each nall with 2 args becomes a nall with all the isall args + 1, that should be at least 3

    var sizeofNall = SIZEOF_C + (isallArgCount + 1) * 2;
    var nallSpacesNeeded = nalls - 1; // -1 because we can always recycle the original isall

    TRACE(' - isall offset=', isallOffset, ', size(isall)=', isallSizeof, ', size(nall)=', sizeofNall, ', there are', nalls, 'nalls[2] and each morphs into a nall[' + isallSizeof + '] so we need', nallSpacesNeeded, 'spaces');
    ASSERT(isallSizeof === sizeofNall, 'both isalls should be a cr-op so should have enough space for this nall');
    var bins;

    if (nallSpacesNeeded) {
      TRACE(' - need additional space; searching for', nallSpacesNeeded, 'spaces of size=', sizeofNall);
      bins = ml_getRecycleOffsets(ml, 0, nallSpacesNeeded, sizeofNall);

      if (!bins) {
        TRACE(' - Was unable to find enough free space to fit', nalls, 'nalls, bailing');
        return false;
      }
    } // If any of the nall args or any of the isall args is 0, then so is R. so collect all args together to defer R


    var allArgs = isallArgs.slice(0);
    var offsetCounter = 0;
    var rewrittenNalls = 0; // Only used in ASSERTs, minifier should eliminate this

    if (nallSpacesNeeded) {
      TRACE(' - starting to morph', nallSpacesNeeded, 'nalls into bins');
      ml_recycles(ml, bins, nallSpacesNeeded, sizeofNall, function (recycledOffset, i, sizeLeft) {
        TRACE('   - using: recycledOffset:', recycledOffset, ', i:', i, ', sizeLeft:', sizeLeft);
        var offset;

        do {
          if (offsetCounter >= countsR) {
            TRACE(' - (last offset must have been offset)');
            return true;
          }

          offset = bounty_getOffset(bounty, indexR, offsetCounter++);
          TRACE('     - offset', offset, 'is isall?', offset === isallOffset);
        } while (offset === isallOffset);

        TRACE('     - offset', offset, 'is not isall so it should be nall');
        ASSERT(ml_dec8(ml, offset) === ML_NALL, 'should be nall');
        ASSERT(offset, 'the earlier loop counted the nalls so it should still have that number of offsets now');
        ASSERT(sizeLeft === ml_getOpSizeSlow(ml, recycledOffset), 'size left should be >=size(op)');

        _trick_isall_nall_1shared_CreateNallAndRemoveNall(ml, indexR, isallArgs.slice(0), allArgs, offset, recycledOffset, sizeLeft);

        ASSERT(++rewrittenNalls);
        return false;
      });
      ASSERT(rewrittenNalls === nallSpacesNeeded, 'should have processed all offsets for R', rewrittenNalls, '==', nallSpacesNeeded, '(', offsetCounter, countsR, ')');
      TRACE(' - all nalls should be morphed now');
    } // Now recycle the isall. have to do it afterwards because otherwise the found recycled bins may be clobbered
    // when eliminating the nall. there's no test for this because it's rather complex to create. sad.


    TRACE(' - recycling the old isall into the last nall');
    var lastNallOffset = bounty_getOffset(bounty, indexR, offsetCounter++);
    if (lastNallOffset === isallOffset) lastNallOffset = bounty_getOffset(bounty, indexR, offsetCounter++);

    _trick_isall_nall_1shared_CreateNallAndRemoveNall(ml, indexR, isallArgs.slice(0), allArgs, lastNallOffset, isallOffset, isallSizeof);

    ASSERT(++rewrittenNalls);
    TRACE('   - deferring', indexR, 'will be R = all?(', allArgs, ')');
    solveStack.push(function (_, force, getDomain, setDomain) {
      TRACE(' - trick_isall_nall_1shared;', indexR, '= all?(', allArgs, ')  ->  ', domain__debug(getDomain(indexR)), '= all?(', allArgs.map(function (index) {
        return domain__debug(getDomain(index));
      }), ')');
      var R = getDomain(indexR);
      allArgs.some(function (index) {
        var X = getDomain(index);

        if (!domain_hasNoZero(X)) {
          // If non-zero, this var wont affect R
          var vX = force(index);

          if (vX === 0) {
            R = domain_removeGtUnsafe(R, 0);
            return true;
          }
        }
      }); // R should be updated properly now. basically if any arg solved to zero, it will be zero. otherwise unchanged.

      ASSERT(R, 'R should have at least a value to solve left');
      setDomain(indexR, R);
    });
    bounty_markVar(bounty, indexR);

    for (var _i11 = 0, l = allArgs.length; _i11 < l; ++_i11) {
      bounty_markVar(bounty, allArgs[_i11]);
    }

    return true;
  }

  function _trick_isall_nall_1shared_CreateNallAndRemoveNall(ml, indexR, nallArgs, allArgs, nallOffset, recycleOffset, recycleSizeof) {
    TRACE(' - _trick_isall_nall_1shared_CreateNallAndRemoveNall: indexR:', indexR, 'nallArgs:', nallArgs, 'allArgs:', allArgs, 'nallOffset:', nallOffset, 'recycleOffset:', recycleOffset, 'recycleSizeof:', recycleSizeof);
    ASSERT(ml_dec16(ml, nallOffset + 1) === 2, 'nalls should have 2 args');
    var indexX = readIndex(ml, nallOffset + OFFSET_C_A);
    var indexY = readIndex(ml, nallOffset + OFFSET_C_B);
    ASSERT(indexX === indexR || indexY === indexR, 'expecting indexR to be part of the nall');
    var index = indexX === indexR ? indexY : indexX;
    TRACE(' - other nall index is', index, domain__debug(getDomain(index, true)));
    nallArgs.push(index);
    allArgs.push(index); // Note: bounty_markVar happens at caller

    TRACE(' - writing a new nall');
    ml_any2c(ml, recycleOffset, recycleSizeof, ML_NALL, nallArgs);

    if (nallOffset !== recycleOffset) {
      TRACE(' - removing the nall because we didnt recycle it');
      ml_eliminate(ml, nallOffset, SIZEOF_C_2);
    }

    ASSERT(ml_validateSkeleton(ml, '_trick_isall_nall_1shared_CreateNallAndRemoveNall'));
  }

  function trick_diff_elimination(diffOffset, indexX, countsX, indexY) {
    // Bascially we "invert" one arg by aliasing it to the other arg and then inverting all ops that relate to it
    // the case with multiple diffs should be eliminated elsewhere
    // all targeted ops should only have 2 args
    // see also the xor elimination (similar to this one)
    // A <= X, X != Y    ->    A !& Y
    // X <= A, X != Y    ->    A | Y
    // X | A, X != Y     ->    Y <= A
    // X !& A, X != Y    ->    A <= Y
    // A -> X, X != Y    ->    A !& Y
    // X -> A, X != Y    ->    A | Y
    TRACE('trick_diff_elimination');
    TRACE(' - index:', indexX, '^', indexY);
    TRACE(' - domains:', domain__debug(getDomain(indexX)), '!=', domain__debug(getDomain(indexY)));
    TRACE(' - meta:', bounty__debugMeta(bounty, indexX), '!=', bounty__debugMeta(bounty, indexY));
    TRACE(' - verying; looking for one DIFF[2], `X != Y` and then we can morph any of these;');
    TRACE('   - LTE_LHS:   X != Y, X <= A     =>    A | Y');
    TRACE('   - LTE_RHS:   X != Y, A <= X     =>    A !& Y');
    TRACE('   - SOME:      X != Y, X | A      =>    Y <= A    =>    Y -> A');
    TRACE('   - NALL:      X != Y, X !& A     =>    A <= Y    =>    A -> Y');
    TRACE('   - IMP_LHS:   X != Y, X -> A     =>    Y | A');
    TRACE('   - IMP_RHS:   X != Y, A -> X     =>    A !& Y'); // First we need to validate. we can only have one diff and all ops can only have 2 args

    ASSERT(countsX < BOUNTY_MAX_OFFSETS_TO_TRACK, 'this was already checked in cut_diff');
    ASSERT(ml_dec16(ml, diffOffset + 1) === 2, 'the diff should be confirmed to have 2 args');

    if (!domain_isBoolyPair(getDomain(indexX))) {
      TRACE(' - X is non-bool, bailing');
      return false;
    } // We need the offsets to eliminate them and to get the "other" var index for each


    var lteLhsOffsets = [];
    var lteLhsArgs = [];
    var lteRhsOffsets = [];
    var lteRhsArgs = [];
    var someOffsets = [];
    var someArgs = [];
    var nallOffsets = [];
    var nallArgs = [];
    var seenDiff = false;
    var impLhsOffsets = [];
    var impLhsArgs = [];
    var impRhsOffsets = [];
    var impRhsArgs = [];
    TRACE(' - scanning', countsX, 'offsets now..');

    for (var i = 0; i < countsX; ++i) {
      var offset = bounty_getOffset(bounty, indexX, i);
      ASSERT(offset, 'the offset should exist...', offset);
      var op = ml_dec8(ml, offset);
      TRACE('   - pos=', i, ', offset=', offset, 'op=', ml__opName(op));
      ASSERT(op === ML_LTE || op === ML_DIFF || op === ML_SOME || op === ML_NALL || op === ML_IMP, 'should be one of these four ops, bounty said so', ml__opName(op));

      if (ml_dec16(ml, offset + 1) !== 2) {
        TRACE(' - op does not have 2 args, bailing');
        return false;
      }

      var indexA = readIndex(ml, offset + OFFSET_C_A);
      var indexB = readIndex(ml, offset + OFFSET_C_B);
      var A = getDomain(indexA, true);
      var B = getDomain(indexB, true);
      ASSERT(indexA === indexX || indexB === indexX, 'bounty should only track ops that use target var');

      if (!domain_isBoolyPair(indexA === indexX ? B : A)) {
        TRACE(' - found an op with a non-bool arg, bailing');
        return false;
      }

      var indexC = indexA === indexX ? indexB : indexA;

      if (op === ML_LTE) {
        // A ^ B, A <= C
        // [00022]^[01],[0022]<=[01]  what if B must end up zero?
        // we have to make sure the lte constraint can not possibly be broken at this point
        if (domain_max(A) > domain_max(B) || domain_min(B) < domain_min(A)) {
          TRACE(' - there are valuations of A and B that could break LTE, bailing because minimizer can fix this');
          requestAnotherCycle = true;
          return false;
        }

        if (indexA === indexX) {
          lteLhsOffsets.push(offset);
          lteLhsArgs.push(indexC);
        } else {
          lteRhsOffsets.push(offset);
          lteRhsArgs.push(indexC);
        }
      } else if (op === ML_IMP) {
        if (indexA === indexX) {
          impLhsOffsets.push(offset);
          impLhsArgs.push(indexC);
        } else {
          impRhsOffsets.push(offset);
          impRhsArgs.push(indexC);
        }
      } else if (op === ML_DIFF) {
        if (diffOffset !== offset) {
          TRACE(' - found a different DIFF, this trick only works on one, bailing');
          return false;
        }

        ASSERT(indexC === indexY);
        seenDiff = true;
      } else if (op === ML_SOME) {
        someOffsets.push(offset);
        someArgs.push(indexC);
      } else {
        ASSERT(op === ML_NALL, 'see assert above');
        nallOffsets.push(offset);
        nallArgs.push(indexC);
      }
    }

    TRACE(' - collection complete; indexY =', indexY, ', diff offset =', diffOffset, ', lte lhs offsets:', lteLhsOffsets, ', lte rhs offsets:', lteRhsOffsets, ', SOME offsets:', someOffsets, ', nall offsets:', nallOffsets, ', imp lhs offsets:', impLhsOffsets, ', imp rhs offsets:', impRhsOffsets);
    ASSERT(seenDiff, 'should have seen a diff, bounty said there would be one'); // Okay. pattern matches. do the rewrite

    TRACE(' - pattern confirmed, morphing ops, removing diff');
    TRACE('   - X != Y, X <= A     =>    A | Y');
    TRACE('   - X != Y, A <= X     =>    A !& Y');
    TRACE('   - X != Y, X | A      =>    Y <= A    =>    Y -> A');
    TRACE('   - X != Y, X !& A     =>    A <= Y    =>    A -> Y');
    TRACE('   - X != Y, X -> A     =>    Y | A');
    TRACE('   - X != Y, A -> X     =>    A !& Y');
    TRACE_MORPH('X != Y', '', 'inverting LTE, SOME, NALL, IMP');
    TRACE(' - processing', lteLhsOffsets.length, 'LTE_LHS ops');

    for (var _i12 = 0, len = lteLhsOffsets.length; _i12 < len; ++_i12) {
      TRACE_MORPH('X <= A, X != Y', 'A | Y');
      var _offset2 = lteLhsOffsets[_i12];
      var index = readIndex(ml, _offset2 + OFFSET_C_A);
      if (index === indexX) index = readIndex(ml, _offset2 + OFFSET_C_B);
      bounty_markVar(bounty, index);
      ASSERT(ml_dec16(ml, _offset2 + 1) === 2, 'should be explicitly checked above');
      ml_c2c2(ml, _offset2, 2, ML_SOME, index, indexY);
    }

    TRACE(' - processing', lteRhsOffsets.length, 'LTE_RHS ops');

    for (var _i13 = 0, _len = lteRhsOffsets.length; _i13 < _len; ++_i13) {
      TRACE_MORPH('X <= A, X != Y', 'A | Y');
      var _offset3 = lteRhsOffsets[_i13];

      var _index5 = readIndex(ml, _offset3 + OFFSET_C_A);

      if (_index5 === indexX) _index5 = readIndex(ml, _offset3 + OFFSET_C_B);
      bounty_markVar(bounty, _index5);
      ASSERT(ml_dec16(ml, _offset3 + 1) === 2, 'should be explicitly checked above');
      ml_c2c2(ml, _offset3, 2, ML_NALL, _index5, indexY);
    } // Note: this bit is kind of redundant (and untested) because it's rewritten and picked up elsewhere


    TRACE(' - processing', someOffsets.length, 'SOME ops');

    for (var _i14 = 0, _len2 = someOffsets.length; _i14 < _len2; ++_i14) {
      TRACE_MORPH('X | A, X != Y', 'Y <= A');
      var _offset4 = someOffsets[_i14];

      var _index6 = readIndex(ml, _offset4 + OFFSET_C_A);

      if (_index6 === indexX) _index6 = readIndex(ml, _offset4 + OFFSET_C_B);
      bounty_markVar(bounty, _index6);
      ASSERT(ml_dec8(ml, _offset4) === ML_SOME, 'right?');
      ASSERT(ml_dec16(ml, _offset4 + 1) === 2, 'should be explicitly checked above');
      ml_c2c2(ml, _offset4, 2, ML_LTE, indexY, _index6);
    }

    TRACE(' - processing', nallOffsets.length, 'NALL ops');

    for (var _i15 = 0, _len3 = nallOffsets.length; _i15 < _len3; ++_i15) {
      TRACE_MORPH('X !& A, X != Y', 'A <= Y');
      var _offset5 = nallOffsets[_i15];

      var _index7 = readIndex(ml, _offset5 + OFFSET_C_A);

      if (_index7 === indexX) _index7 = readIndex(ml, _offset5 + OFFSET_C_B);
      bounty_markVar(bounty, _index7);
      ASSERT(ml_dec16(ml, _offset5 + 1) === 2, 'should be explicitly checked above');
      ml_c2c2(ml, _offset5, 2, ML_LTE, _index7, indexY);
    }

    TRACE(' - processing', impLhsOffsets.length, 'IMP_LHS ops');

    for (var _i16 = 0, _len4 = impLhsOffsets.length; _i16 < _len4; ++_i16) {
      TRACE_MORPH('X -> A, X != Y', 'A | Y');
      var _offset6 = impLhsOffsets[_i16];

      var _index8 = readIndex(ml, _offset6 + OFFSET_C_A);

      if (_index8 === indexX) _index8 = readIndex(ml, _offset6 + OFFSET_C_B);
      bounty_markVar(bounty, _index8);
      ASSERT(ml_dec16(ml, _offset6 + 1) === 2, 'should be explicitly checked above');
      ml_c2c2(ml, _offset6, 2, ML_SOME, _index8, indexY);
    }

    TRACE(' - processing', impRhsOffsets.length, 'IMP_RHS ops');

    for (var _i17 = 0, _len5 = impRhsOffsets.length; _i17 < _len5; ++_i17) {
      TRACE_MORPH('X -> A, X != Y', 'A | Y');
      var _offset7 = impRhsOffsets[_i17];

      var _index9 = readIndex(ml, _offset7 + OFFSET_C_A);

      if (_index9 === indexX) _index9 = readIndex(ml, _offset7 + OFFSET_C_B);
      bounty_markVar(bounty, _index9);
      ASSERT(ml_dec16(ml, _offset7 + 1) === 2, 'should be explicitly checked above');
      ml_c2c2(ml, _offset7, 2, ML_NALL, _index9, indexY);
    }

    TRACE(' - and finally removing the DIFF');
    ASSERT(ml_dec16(ml, diffOffset + 1) === 2, 'diff should have 2 args here');
    ml_eliminate(ml, diffOffset, SIZEOF_C_2);
    TRACE(' - X is a leaf constraint, defer it', indexX);
    leafs.push(indexX);
    solveStack.push(function (_, force, getDomain, setDomain) {
      var X = getDomain(indexX);
      var Y = getDomain(indexY);
      TRACE(' - diff + ops...;', indexX, '!=', indexY, '  ->  ', domain__debug(X), '!=', domain__debug(getDomain(indexY))); // TRACE(' - X:',domain__debug(X));
      // TRACE(' - Y:',domain__debug(getDomain(indexY)));
      // TRACE(' - ltelhs:', lteLhsArgs.map(a=>domain__debug(getDomain(a))));
      // TRACE(' - lterhs:', lteRhsArgs.map(a=>domain__debug(getDomain(a))));
      // TRACE(' - some:', someArgs.map(a=>domain__debug(getDomain(a))));
      // TRACE(' - nall:', nallArgs.map(a=>domain__debug(getDomain(a))));
      // TRACE(' - implhs:', impLhsArgs.map(a=>domain__debug(getDomain(a))));
      // TRACE(' - imprhs:', impRhsArgs.map(a=>domain__debug(getDomain(a))));

      var oX = X;
      var minX = domain_min(X);
      var maxX = domain_max(X);
      TRACE('  - applying', lteLhsArgs.length, 'LTELHSs (X <= vars)');

      for (var _i18 = 0; _i18 < lteLhsArgs.length; ++_i18) {
        // X <= D
        var _index10 = lteLhsArgs[_i18];
        var D = getDomain(_index10);
        TRACE('    - index:', _index10, ', domain:', domain__debug(D));
        var minD = domain_min(D);

        if (maxX > minD) {
          var maxD = domain_max(D); // At least one value of X is larger than a value in D so there is currently
          // a valuation of X and D that violates the LTE and we must fix that.

          if (maxD >= maxX) {
            // There are values in D that are larger-eq to all values in X. use them.
            // just remove the intersecting values from D and then lte should satisfy
            D = domain_removeLtUnsafe(D, maxX);
            setDomain(_index10, D);
          } else {
            // The largest value of D is smaller than the largest X
            // maximize D then remove any value from X larger than that
            D = domain_intersectionValue(D, maxD);
            setDomain(_index10, D);
            X = domain_removeGtUnsafe(X, maxD);
          }

          ASSERT(D);
          ASSERT(X);
          ASSERT(domain_max(X) <= domain_min(D));
        }
      }

      TRACE('   - X after LTELHSs:', domain__debug(X));
      TRACE('  - applying', lteRhsArgs.length, 'LTERHSs (vars <= X)');

      for (var _i19 = 0; _i19 < lteRhsArgs.length; ++_i19) {
        // D <= X
        var _index11 = lteRhsArgs[_i19];

        var _D4 = getDomain(_index11);

        TRACE('    - index:', _index11, ', domain:', domain__debug(_D4));

        var _maxD = domain_max(_D4);

        if (minX < _maxD) {
          // At least one value in X is smaller than a value in D so there is currently
          // a valuation of X and D that violates the LTE and we must fix that.
          var _minD = domain_min(_D4);

          if (_minD <= minX) {
            // There are values in D that are smaller-eq to all values in X. use them.
            // just remove the intersecting values from D and then lte should satisfy
            _D4 = domain_removeGtUnsafe(_D4, minX);
            setDomain(_index11, _D4);
          } else {
            // The smallest value of D is larger than the smallest X
            // minimze D then remove any value from X smaller than that
            _D4 = domain_intersectionValue(_D4, _minD);
            setDomain(_index11, _D4);
            X = domain_removeLtUnsafe(X, _maxD);
          }
        }

        ASSERT(_D4);
        ASSERT(X);
        ASSERT(domain_max(_D4) <= domain_min(X));
      }

      TRACE('   - X after LTERHSs:', domain__debug(X)); // Reminder: these are pairs. some(X D) for each d in someArgs

      for (var _i20 = 0; _i20 < someArgs.length; ++_i20) {
        // Some(X ...)
        var _index12 = someArgs[_i20];

        var _D5 = getDomain(_index12);

        TRACE('    - index:', _index12, ', domain:', domain__debug(getDomain(_index12)));

        if (domain_isZero(_D5)) {
          // X must be nonzero now
          X = domain_removeValue(X, 0);
        } else if (domain_hasZero(_D5)) {
          ASSERT(domain_isBooly(_D5), 'assuming D isnt empty, and it wasnt zero but has a zero, it should be a booly');
          _D5 = domain_removeValue(_D5, 0);
          setDomain(_index12, _D5);
        }

        ASSERT(X);
        ASSERT(_D5);
        ASSERT(domain_hasNoZero(X) || domain_hasNoZero(_D5));
      }

      TRACE('   - X after SOMEs:', domain__debug(X)); // Reminder: these are pairs. nall(X D) for each d in nallArgs

      for (var _i21 = 0; _i21 < nallArgs.length; ++_i21) {
        // Nall(X ...)
        var _index13 = nallArgs[_i21];

        var _D6 = getDomain(_index13);

        TRACE('    - index:', _index13, ', domain:', domain__debug(_D6));

        if (domain_hasNoZero(_D6)) {
          // X must be zero
          X = domain_removeGtUnsafe(X, 0);
        } else if (domain_hasNoZero(_D6)) {
          ASSERT(domain_isBooly(_D6), 'assuming D isnt empty, and it wasnt nonzero, it should be a booly');
          _D6 = domain_removeGtUnsafe(_D6, 0);
          setDomain(_index13, _D6);
        }

        ASSERT(X);
        ASSERT(_D6);
        ASSERT(domain_isZero(X) || domain_isZero(_D6));
      }

      TRACE('   - X after NALLs:', domain__debug(X));

      for (var _i22 = 0; _i22 < impLhsArgs.length; ++_i22) {
        // X -> D
        var _index14 = impLhsArgs[_i22];

        var _D7 = getDomain(_index14);

        TRACE('    - index:', _index14, ', domain:', domain__debug(_D7)); // The easiest out is that D is either nonzero or that X is zero

        if (!domain_hasNoZero(_D7) && !domain_isZero(X)) {
          if (domain_isZero(_D7)) {
            // X must be zero otherwise the implication doesnt hold
            X = domain_removeGtUnsafe(X, 0);
          } else if (domain_hasNoZero(_D7)) {
            // X must be nonzero because D is nonzero
            X = domain_removeValue(X, 0);
          } else {
            ASSERT(domain_isBooly(_D7)); // Setting D to nonzero is the safest thing to do

            setDomain(_index14, domain_removeValue(_D7, 0));
          }
        }

        ASSERT(X);
        ASSERT(_D7);
        ASSERT(domain_hasNoZero(X) ? domain_hasNoZero(_D7) : true);
        ASSERT(domain_isZero(_D7) ? domain_isZero(X) : true);
        ASSERT(domain_isSolved(_D7) || domain_isZero(X), 'if X is zero then D doesnt matter. if D is solved then X is asserted to be fine above');
      }

      TRACE('   - X after IMPLHSs:', domain__debug(X));

      for (var _i23 = 0; _i23 < impRhsArgs.length; ++_i23) {
        // D -> X
        var _index15 = impRhsArgs[_i23];

        var _D8 = getDomain(_index15);

        TRACE('    - index:', _index15, ', domain:', domain__debug(_D8));

        if (domain_hasNoZero(_D8)) {
          // X must be nonzero
          X = domain_removeGtUnsafe(X, 0);
        } else if (domain_isBooly(_D8)) {
          // Safest value for imp-lhs is 0
          _D8 = domain_removeValue(_D8, 0);
        }

        ASSERT(X);
        ASSERT(_D8);
        ASSERT(domain_hasNoZero(_D8) ? domain_hasNoZero(X) : true);
        ASSERT(domain_isZero(X) ? domain_isZero(_D8) : true);
        ASSERT(domain_isSolved(X) || domain_isZero(_D8), 'if D is zero then X doesnt matter. if X is solved then D is asserted to be fine above');
      }

      TRACE('   - X after IMPRHSs:', domain__debug(X)); // X != Y

      TRACE(' - != Y:', domain__debug(getDomain(indexY)));

      if (domain_isSolved(X)) {
        Y = domain_removeValue(Y, domain_getValue(X));
        setDomain(indexY, Y);
      } else {
        X = domain_removeValue(X, force(indexY));
      }

      TRACE('   - X after DIFFs:', domain__debug(X));
      ASSERT(X, 'X should be able to reflect any solution');
      if (X !== oX) setDomain(indexX, X);
    });
    bounty_markVar(bounty, indexX);
    bounty_markVar(bounty, indexY);
    somethingChanged();
    return true;
  }

  function trick_xor_elimination(xorOffset, indexX, countsX, indexY) {
    // The xor is basically a diff (!=) in a booly sense. so we can invert all the affected ops by inverting the xor.
    // bascially we "invert" a xor by aliasing one arg to the other arg and then inverting all ops that relate to it
    // all targeted ops should only have 2 args
    // X | A, X ^ Y     ->    Y <= A
    // X !& A, X ^ Y    ->    A <= Y
    // A -> X, X ^ Y    ->    A !& Y
    // X -> A, X ^ Y    ->    A | Y
    // note: eligible LTEs must be morphed to an implication first
    // A <= X, X ^ Y    ->    A !& Y
    // X <= A, X ^ Y    ->    A | Y
    TRACE('trick_xor_elimination');
    TRACE(' - index:', indexX, '^', indexY);
    TRACE(' - domains:', domain__debug(getDomain(indexX)), '^', domain__debug(getDomain(indexY)));
    TRACE(' - meta:', bounty__debugMeta(bounty, indexX), '^', bounty__debugMeta(bounty, indexY));
    TRACE(' - verying; looking for a XOR, `X ^ Y` and then we can morph any of these;'); // TRACE('   - LTE_LHS:   X ^ Y, X <= A     =>    A | Y');
    // TRACE('   - LTE_RHS:   X ^ Y, A <= X     =>    A !& Y');

    TRACE('   - SOME:      X ^ Y, X | A      =>    Y <= A    =>    Y -> A');
    TRACE('   - NALL:      X ^ Y, X !& A     =>    A <= Y    =>    A -> Y');
    TRACE('   - IMP_LHS:   X ^ Y, X -> A     =>    Y | A');
    TRACE('   - IMP_RHS:   X ^ Y, A -> X     =>    A !& Y');
    TRACE(' - all args must be booly pairs, or bounty-booly without LTE');
    ASSERT(countsX < BOUNTY_MAX_OFFSETS_TO_TRACK, 'this was already checked in cut_xor');
    ASSERT(ml_dec16(ml, xorOffset + 1) === 2, 'XORs only have two args');

    if (!domain_isBooly(getDomain(indexX))) {
      TRACE(' - X is non-bool, bailing');
      return false;
    } // We need the offsets to eliminate them and to get the "other" var index for each
    // first we need to validate.
    // - we can only have one XOR
    // - all ops must have 2 args
    // - the "other" arg must also be a booly-pair or bounty-booly


    var someOffsets = [];
    var nallOffsets = [];
    var seenXor = false;
    var impLhsOffsets = [];
    var impRhsOffsets = [];

    for (var i = 0; i < countsX; ++i) {
      var offset = bounty_getOffset(bounty, indexX, i);
      ASSERT(offset, 'the offset should exist...', offset);
      var op = ml_dec8(ml, offset);
      ASSERT(op === ML_XOR || op === ML_SOME || op === ML_NALL || op === ML_IMP, 'should be one of these four ops, bounty said so', ml__opName(op));

      if (ml_dec16(ml, offset + 1) !== 2) {
        TRACE(' - op', ml__opName(op), 'does not have 2 args (', ml_dec16(ml, offset + 1), '), bailing');
        return false;
      }

      var indexA = readIndex(ml, offset + OFFSET_C_A);
      var indexB = readIndex(ml, offset + OFFSET_C_B);
      ASSERT(indexA === indexX || indexB === indexX, 'bounty should only track ops that use target var');
      TRACE('    - current offset:', offset, ', op:', ml__opName(op), 'indexes:', indexA, indexB, ', domains:', domain__debug(getDomain(indexA, true)), domain__debug(getDomain(indexB, true))); // Get pair

      var indexT = indexA === indexX ? indexB : indexA;

      if (bounty_getCounts(bounty, indexT) === 0) {
        TRACE(' - an arg was marked (counts=0), bailing (we will get this in the rebound)'); // Note: while there may be other ops that could be converted, we'll
        // get at least one more cutter pass and we'll eventually retry this

        return false;
      }

      var T = getDomain(indexT, true);

      if (!domain_isBoolyPair(T) && hasFlags(bounty_getMeta(bounty, indexT), BOUNTY_FLAG_NOT_BOOLY)) {
        TRACE(' - found an "other" var that was marked not booly in its meta and not a booly pair, bailing');
        return false;
      }

      if (op === ML_IMP) {
        if (indexA === indexX) {
          if (impLhsOffsets.indexOf(offset) < 0) impLhsOffsets.push(offset);
        } else if (impRhsOffsets.indexOf(offset) < 0) impRhsOffsets.push(offset);
      } else if (op === ML_XOR) {
        if (xorOffset !== offset) {
          TRACE(' - found a different XOR, this trick only works on one, bailing');
          return false;
        }

        seenXor = true;
      } else if (op === ML_SOME) {
        if (ml_dec16(ml, offset + 1) !== 2) {
          TRACE(' - There was a SOME that did not have 2 args, bailing');
        }

        if (someOffsets.indexOf(offset) < 0) someOffsets.push(offset);
      } else {
        ASSERT(op === ML_NALL, 'see assert above');
        if (nallOffsets.indexOf(offset) < 0) nallOffsets.push(offset);
      }
    }

    TRACE(' - collection complete; indexY =', indexY, ', XOR offset =', xorOffset, ', SOME offsets:', someOffsets, ', NALL offsets:', nallOffsets, ', IMP_LHS offsets:', impLhsOffsets, ', IMP_RHS offsets:', impRhsOffsets);
    ASSERT(seenXor, 'should have seen a XOR, bounty said there would be one'); // Okay. pattern matches. do the rewrite

    TRACE(' - pattern confirmed, morphing ops, removing XOR'); // TRACE('   - X ^ Y, X <= A     =>    A | Y');
    // TRACE('   - X ^ Y, A <= X     =>    A !& Y');

    TRACE('   - X ^ Y, X | A      =>    Y -> A; offsets:', someOffsets);
    TRACE('   - X ^ Y, X !& A     =>    A -> Y; offsets:', nallOffsets);
    TRACE('   - X ^ Y, X -> A     =>    Y | A; offsets:', impLhsOffsets);
    TRACE('   - X ^ Y, A -> X     =>    A !& Y; offsets:', impRhsOffsets);
    TRACE_MORPH('X ^ Y, inverting LTE, SOME, NALL, IMP', '');
    TRACE(' - processing', someOffsets.length, 'SOME ops');

    for (var _i24 = 0, len = someOffsets.length; _i24 < len; ++_i24) {
      // X | A, X != Y    ->    Y <= A
      var _offset8 = someOffsets[_i24];
      var index = readIndex(ml, _offset8 + OFFSET_C_A);
      if (index === indexX) index = readIndex(ml, _offset8 + OFFSET_C_B);
      bounty_markVar(bounty, index);
      ASSERT(ml_dec8(ml, _offset8) === ML_SOME, 'right?');
      ASSERT(ml_dec16(ml, _offset8 + 1) === 2, 'should be explicitly checked above');
      ml_c2c2(ml, _offset8, 2, ML_IMP, indexY, index);
    }

    TRACE(' - processing', nallOffsets.length, 'NALL ops');

    for (var _i25 = 0, _len6 = nallOffsets.length; _i25 < _len6; ++_i25) {
      // X !& A, X != Y    ->    A <= Y
      var _offset9 = nallOffsets[_i25];

      var _index16 = readIndex(ml, _offset9 + OFFSET_C_A);

      if (_index16 === indexX) _index16 = readIndex(ml, _offset9 + OFFSET_C_B);
      bounty_markVar(bounty, _index16);
      ASSERT(ml_dec16(ml, _offset9 + 1) === 2, 'should be explicitly checked above');
      ml_c2c2(ml, _offset9, 2, ML_IMP, _index16, indexY);
    }

    TRACE(' - processing', impLhsOffsets.length, 'IMP_LHS ops');

    for (var _i26 = 0, _len7 = impLhsOffsets.length; _i26 < _len7; ++_i26) {
      // X -> A, X != Y    ->    A | Y
      var _offset10 = impLhsOffsets[_i26];

      var _index17 = readIndex(ml, _offset10 + OFFSET_C_A);

      if (_index17 === indexX) _index17 = readIndex(ml, _offset10 + OFFSET_C_B);
      bounty_markVar(bounty, _index17);
      ASSERT(ml_dec16(ml, _offset10 + 1) === 2, 'should be explicitly checked above');
      ml_c2c2(ml, _offset10, 2, ML_SOME, _index17, indexY);
    }

    TRACE(' - processing', impRhsOffsets.length, 'IMP_RHS ops');

    for (var _i27 = 0, _len8 = impRhsOffsets.length; _i27 < _len8; ++_i27) {
      // X -> A, X != Y    ->    A | Y
      var _offset11 = impRhsOffsets[_i27];

      var _index18 = readIndex(ml, _offset11 + OFFSET_C_A);

      if (_index18 === indexX) _index18 = readIndex(ml, _offset11 + OFFSET_C_B);
      bounty_markVar(bounty, _index18);
      ASSERT(ml_dec16(ml, _offset11 + 1) === 2, 'should be explicitly checked above');
      ml_c2c2(ml, _offset11, 2, ML_NALL, _index18, indexY);
    }

    TRACE(' - and finally removing the XOR');
    ASSERT(ml_dec16(ml, xorOffset + 1) === 2, 'diff should have 2 args here');
    ml_eliminate(ml, xorOffset, SIZEOF_C_2);
    TRACE(' - X is a leaf constraint, defer it', indexX);
    leafs.push(indexX);
    solveStack.push(function (_, force, getDomain, setDomain) {
      var X = getDomain(indexX);
      TRACE(' - xor + ops...;', indexX, '^', indexY, '  ->  ', domain__debug(X), '^', domain__debug(getDomain(indexY)));

      if (force(indexY) === 0) {
        X = domain_removeValue(X, 0);
      } else {
        X = domain_removeGtUnsafe(X, 0);
      }

      ASSERT(X, 'X should be able to reflect any solution');
      setDomain(indexX, X);
    });
    bounty_markVar(bounty, indexX);
    bounty_markVar(bounty, indexY);
    somethingChanged();
    return true;
  }

  function trick_diff_xor(ml, diffOffset, indexX, countsX, indexA) {
    TRACE('trick_diff_xor');
    TRACE(' - X != A, X ^ B    =>    X!=A,A==B'); // Find the xor. X may a counts > 2

    var xorOffset = 0;

    for (var i = 0; i < countsX; ++i) {
      var offset = bounty_getOffset(bounty, indexX, i);

      if (ml_dec8(ml, offset) === ML_XOR) {
        xorOffset = offset;
      }
    }

    ASSERT(xorOffset, 'bounty said there was at least one xor', xorOffset);

    if (ml_dec16(ml, xorOffset + 1) !== 2) {
      TRACE(' - the XOR did not have 2 args, bailing');
      return false;
    }

    ASSERT(readIndex(ml, xorOffset + OFFSET_C_A) === indexX || readIndex(ml, xorOffset + OFFSET_C_B) === indexX, 'X should be part of XOR');
    var indexB = readIndex(ml, xorOffset + OFFSET_C_A);
    if (indexB === indexX) indexB = readIndex(ml, xorOffset + OFFSET_C_B);
    var A = getDomain(indexA, true);
    var B = getDomain(indexB, true);
    var X = getDomain(indexX, true);
    TRACE(' - indexes:', indexX, '!=', indexA, ',', indexX, '^', indexB);
    TRACE(' - domains:', domain__debug(X), '!=', domain__debug(A), ',', domain__debug(X), '^', domain__debug(B));

    if (!domain_isBoolyPair(A) || !domain_isBoolyPair(B) || domain_intersection(X, A) !== A || domain_intersection(X, B) !== B) {
      // Note: this implicitly tested whether A is a booly
      TRACE(' - A or B wasnt a boolypair or A did not contain all values, bailing');
      return false;
    }

    TRACE(' - pattern confirmed');
    TRACE_MORPH('X != A, X ^ B', 'X ^ A, A == B');
    ml_eliminate(ml, diffOffset, SIZEOF_C_2);
    cutAddPseudoBoolyAlias(indexB, indexA);
    somethingChanged();
    return true;
  }

  function trick_diff_alias(indexX, indexY, countsX) {
    TRACE('trick_diff_alias; index X:', indexX, ', index Y:', indexY, ', counts:', countsX);
    TRACE(' - X!=A,X!=B, size(A)==2,min(A)==min(B),max(A)==max(B)   =>   A==B');
    var X = getDomain(indexX);
    var Y = getDomain(indexY);
    TRACE(' - domains:', domain__debug(X), domain__debug(Y), '(trick only works if these are equal and size=2)');

    if (X === Y && domain_size(X) === 2) {
      // If we can find another diff on X where the domain is also equal to X, we can alias Y to that var
      for (var i = 0; i < countsX; ++i) {
        var offset = bounty_getOffset(bounty, indexX, i);
        ASSERT(offset, 'the offset should exist...', offset);
        var op = ml_dec8(ml, offset);
        TRACE('   - checking offset=', offset, 'op=', op, op === ML_DIFF);

        if (op === ML_DIFF) {
          var count = ml_dec16(ml, offset + 1);
          TRACE('     - is diff with', count, 'indexes');

          if (count !== 2) {
            TRACE('       - count must be 2 for this to work, moving to next op');
            continue;
          }

          var indexA = readIndex(ml, offset + OFFSET_C_A);
          var indexB = readIndex(ml, offset + OFFSET_C_B);
          TRACE(' - indexes:', indexA, indexB, ', domains:', domain__debug(getDomain(indexA)), domain__debug(getDomain(indexB)));
          ASSERT(indexA === indexX || indexB === indexX, 'xor should have X as either arg because bounty said so');
          var indexZ = void 0;

          if (indexA === indexX) {
            if (indexB === indexY) continue;
            indexZ = indexB;
          } else {
            ASSERT(indexB === indexX, 'x should match at least one side');
            if (indexA === indexY) continue;
            indexZ = indexA;
          }

          TRACE('     - not original diff, Z=', indexZ);
          ASSERT(indexY !== indexZ, 'deduper should have eliminated duplicate diffs');
          var Z = getDomain(indexZ);

          if (X === Z) {
            TRACE('     - domains are equal so X!=Y, X!=Z, with X==Y==Z, with size(X)=2, so Y=Z, index', indexY, '=', indexZ);
            TRACE('     - eliminating this diff, aliasing Z to Y');
            ASSERT(Y === Z);
            ASSERT(domain_size(Z) === 2); // No solve stack required, indexY == indexZ

            addAlias(indexZ, indexY, 'double bin diff');
            ml_eliminate(ml, offset, SIZEOF_C_2);
            bounty_markVar(bounty, indexX);
            bounty_markVar(bounty, indexY);
            bounty_markVar(bounty, indexZ);
            somethingChanged();
            return true;
          }
        }
      }
    }

    TRACE(' - unable to apply trick_diff_alias, bailing');
    return false;
  }

  function trick_xor_alias(indexX, indexY, countsX, Y, sizeY, YisBooly) {
    TRACE('trick_xor_alias; index X:', indexX, ', index Y:', indexY, ', counts:', countsX, ', sizeY:', sizeY);
    ASSERT(indexX !== indexY, 'X^Y is falsum and shouldnt occur here'); // We are looking for `X^Y,X^B` and if `size(A)==2,dA==dB` or B is a booly then we alias them

    var YisPair = sizeY === 2;
    TRACE(' - domains:', domain__debug(getDomain(indexX)), domain__debug(Y), 'Y is booly var?', YisBooly, ', Y size?', sizeY);

    if (!YisBooly && !YisPair) {
      TRACE(' - Y is neither a booly var nor a pair so cant apply this trick; bailing');
      return false;
    } // We now search for any xor that uses x but not y as z
    // the first z to match YisBooly or domain y==z will be aliased


    for (var i = 0; i < countsX; ++i) {
      var offset = bounty_getOffset(bounty, indexX, i);
      ASSERT(offset, 'the offset should exist...', offset);
      var op = ml_dec8(ml, offset);
      TRACE('   - checking offset=', offset, 'op=', op, op === ML_XOR);

      if (op === ML_XOR) {
        var indexA = readIndex(ml, offset + OFFSET_C_A);
        var indexB = readIndex(ml, offset + OFFSET_C_B);
        TRACE('     - is xor, indexes:', indexA, indexB, 'confirming its not the input X and Y', indexX, indexY, '( -> it', indexX === indexA && indexY === indexB || indexX === indexB && indexY === indexA ? 'is' : 'isnt', ')');
        ASSERT(indexA === indexX || indexB === indexX, 'at least one argument should match X since it is X-es bounty');
        var indexZ = void 0;

        if (indexA === indexX) {
          if (indexB === indexY) continue;
          indexZ = indexB;
        } else if (indexB === indexX) {
          if (indexA === indexY) continue;
          indexZ = indexA;
        } else {
          THROW('X should be left or right of its xors');
        }

        ASSERT(indexY !== indexZ, 'deduper should have eliminated duplicate xors', indexX, indexY, indexA, indexB);
        var aliased = false;
        var Z = getDomain(indexZ, true);

        if (YisPair && Z === Y) {
          TRACE(' - true aliases. X^Y X^Z, ' + indexX + '^' + indexY + ' ' + indexX + '^' + indexZ + ', aliasing', indexZ, 'to', indexY); // Keep the current xor (X^Y) and drop the found xor (X^Z)

          addAlias(indexZ, indexY);
          aliased = true;
        } else if (YisPair && domain_size(Z) === 2) {
          TRACE(' - pseudo aliases. X^Y X^Z, ' + indexX + '^' + indexY + ' ' + indexX + '^' + indexZ + ', aliasing', indexZ, 'to', indexY);
          TRACE(' - since Y and Z can only be "zero or nonzero", the xor forces them to pick either the zero or nonzero value, regardless of anything else'); // Keep the current xor (X^Y) and drop the found xor (X^Z)

          cutAddPseudoBoolyAlias(indexY, indexZ);
          aliased = true;
        } else if (YisBooly) {
          var metaZ = getMeta(bounty, indexZ, true); // Keep booly flag

          TRACE(' - Z isnt a pair, checking meta for booly:', bounty__debugMeta(bounty, indexZ));

          if (!hasFlags(metaZ, BOUNTY_FLAG_NOT_BOOLY)) {
            TRACE(' - Y and Z are both booly and xor on the same variable. so this is a pseudo alias. slash the found xor.'); // Keep the current xor (X^Y) and drop the found xor (X^Z)

            cutAddPseudoBoolyAlias(indexY, indexZ);
            aliased = true;
          }
        }

        if (aliased) {
          TRACE(' - Y was aliased to Z, eliminating this xor and returning');
          ml_eliminate(ml, offset, SIZEOF_C_2);
          bounty_markVar(bounty, indexX);
          bounty_markVar(bounty, indexY); // The alias will mess up Y counts

          bounty_markVar(bounty, indexZ);
          somethingChanged();
          return true;
        }

        TRACE(' - Z did not match. moving to next constraint');
      }
    }

    TRACE('  - did not find a second xor; bailing');
    return false;
  }

  function trick_isall_xor(indexA, indexB, xorOffset, countsA, countsB) {
    TRACE('trick_isall_xor; index A:', indexA, ', index B:', indexB, ', counts:', countsA, countsB);
    ASSERT(countsA === 2, 'check function if this changes', countsA, countsB); // R^A, R=all?(X Y Z)  ->   A=nall(X Y Z)
    // the xor kind of acts like a diff in this case so we flip the isall to become a isnall on xor's other arg
    // we defer R to be xor A in the solvestack

    TRACE(' - first searching for isall op');

    for (var i = 0; i < countsA; ++i) {
      var offset = bounty_getOffset(bounty, indexA, i);
      ASSERT(offset, 'there should be as many offsets as counts unless that exceeds the max and that has been checked already');

      if (offset !== xorOffset) {
        var opcode = ml_dec8(ml, offset);

        if (opcode === ML_ISALL) {
          TRACE(' - found isall at', offset);
          return _trick_isall_xor(indexA, indexB, xorOffset, offset);
        }
      }
    }

    THROW('bounty should have asserted that an isall existed');
  }

  function _trick_isall_xor(indexR, indexB, xorOffset, isallOffset) {
    TRACE_MORPH('R^S, R=all?(X Y Z ...)', 'S=nall(X Y Z ...)');
    TRACE(' - _trick_isall_xor: now applying morph to isall and eliminating the xor'); // Note: R only has 2 counts

    var isallArgCount = ml_dec16(ml, isallOffset + 1);
    ASSERT(getAlias(ml_dec16(ml, isallOffset + SIZEOF_C + isallArgCount * 2)) === indexR); // Morph the isall to an isnall (simply change the op) on B. dont forget to mark all its args

    ml_enc8(ml, isallOffset, ML_ISNALL);
    ml_enc16(ml, isallOffset + SIZEOF_C + isallArgCount * 2, indexB);
    ml_eliminate(ml, xorOffset, SIZEOF_C_2); // A of xor is R of isall. defer resolving the xor because B of xor
    // is going to be the new R of the isall-flipped-to-isnall

    solveStack.push(function (_, force, getDomain, setDomain) {
      TRACE(' - _trick_isall_xor');
      var R = getDomain(indexR);
      var B = getDomain(indexB);
      TRACE(' -', domain__debug(R), '^', domain__debug(B)); // Since S is solved according to "not isall", we only have to force R^S here
      // (we didnt eliminate the isall, we just transformed it)

      ASSERT(domain_isBooly(R));
      if (domain_isBooly(B)) B = domain_createValue(force(indexB));

      if (domain_isZero(B)) {
        R = domain_removeValue(R, 0);
      } else {
        ASSERT(domain_hasNoZero(B));
        R = domain_removeGtUnsafe(R, 0);
      }

      setDomain(indexR, R);
      ASSERT(getDomain(indexR));
      ASSERT(getDomain(indexB));
      ASSERT(!domain_isBooly(getDomain(indexR)) && !domain_isBooly(getDomain(indexB)));
      ASSERT(domain_isZero(getDomain(indexR)) !== domain_isZero(getDomain(indexB)));
    });
    bounty_markVar(bounty, indexR); // R

    bounty_markVar(bounty, indexB);
    markAllArgs(ml, isallOffset, isallArgCount);
    somethingChanged();
    return true;
  }

  function trick_issome_xor(indexA, indexR, xorOffset, countsA, countsB) {
    TRACE('trick_issome_xor; index A:', indexA, ', index R:', indexR, ', counts:', countsA, countsB);
    TRACE(' - A^R, R=all?(X Y Z)  ->   A=nall(X Y Z)'); // The xor kind of acts like a diff in this case so we flip the isall to become a isnone
    // and use A as the new result var for that isnone

    TRACE(' - first searching for issome op');

    for (var i = 0; i < countsA; ++i) {
      var offset = bounty_getOffset(bounty, indexA, i);

      if (offset !== xorOffset) {
        var opcode = ml_dec8(ml, offset);

        if (opcode === ML_ISSOME) {
          TRACE(' - found issome at', offset);
          return _trick_issome_xor(indexA, indexR, xorOffset, offset);
        }
      }
    }

    THROW('bounty should have asserted that an issome existed');
  }

  function _trick_issome_xor(indexR, indexA, xorOffset, issomeOffset) {
    TRACE(' - _trick_issome_xor: now applying morph to issome and eliminating the xor');
    TRACE_MORPH('A^R, R=all?(X Y Z)', 'A=nall(X Y Z)');
    var issomeArgCount = ml_dec16(ml, issomeOffset + 1);
    var issomeResultOffset = issomeOffset + SIZEOF_C + issomeArgCount * 2;
    ASSERT(indexR === readIndex(ml, issomeResultOffset), 'asserted before');
    var issomeArgs = markAndCollectArgs(ml, issomeOffset, issomeArgCount);
    bounty_markVar(bounty, indexA);
    bounty_markVar(bounty, indexR); // Morph the issome to an isnone (simply change the op). dont forget to mark all its args

    ml_enc8(ml, issomeOffset, ML_ISNONE);
    ml_enc16(ml, issomeResultOffset, indexA);
    ml_eliminate(ml, xorOffset, SIZEOF_C_2);
    solveStack.push(function (_, force, getDomain, setDomain) {
      TRACE(' - trick_issome_xor');
      var A = getDomain(indexA);
      var R = getDomain(indexR);
      TRACE(' -', domain__debug(A), '^', domain__debug(R));

      if (domain_isZero(A)) {
        TRACE(' - A=0 so R must >0');
        R = domain_removeValue(R, 0);
        setDomain(indexR, R);
      } else if (domain_isZero(R)) {
        TRACE(' - R=0 so A must >0');
        A = domain_removeGtUnsafe(A, 0);
        setDomain(indexA, A);
      } else if (domain_hasNoZero(A)) {
        TRACE(' - A>0 so R must =0');
        R = domain_removeGtUnsafe(R, 0);
        setDomain(indexR, R);
      } else if (domain_hasNoZero(R)) {
        TRACE(' - R>0 so A must =0');
        A = domain_removeGtUnsafe(A, 0);
        setDomain(indexA, A);
      } else {
        ASSERT(domain_isBooly(A) && domain_isBooly(R));
        var allNone = true;
        var some = false;
        var boolyIndex = -1;

        for (var i = 0; i < issomeArgs.lenght; ++i) {
          var index = issomeArgs[i];
          var D = getDomain(index);

          if (domain_hasNoZero(D)) {
            some = true;
            break;
          } else if (!domain_isZero(D)) {
            allNone = false;
            boolyIndex = i;
          }
        }

        if (some) {
          TRACE(' - found at least one arg that was nonzero, R>0');
          R = domain_removeValue(R, 0);
        } else if (allNone) {
          TRACE(' - all args were zero, R=0');
          R = domain_removeGtUnsafe(R, 0);
        } else {
          TRACE(' - found no nonzero and at least one arg was booly, forcing R>0 and that arg >0 as well');
          R = domain_removeValue(R, 0);
          var _index19 = issomeArgs[boolyIndex];

          var _D9 = getDomain(_index19);

          ASSERT(domain_isBooly(_D9), 'we. just. checked. this');
          _D9 = domain_removeValue(_D9, 0);
          ASSERT(_D9);
          setDomain(_index19, _D9);
        }

        setDomain(indexR, R);
      }

      ASSERT(getDomain(indexA));
      ASSERT(getDomain(indexR));
      ASSERT(!domain_isBooly(getDomain(indexA)) && !domain_isBooly(getDomain(indexR)));
      ASSERT(domain_isZero(getDomain(indexA)) !== domain_isZero(getDomain(indexR)));
      ASSERT(domain_hasNoZero(getDomain(indexR)) === issomeArgs.some(function (i) {
        return domain_hasNoZero(getDomain(i));
      }));
    });
    somethingChanged();
    return true;
  }

  function trick_some_xor(indexX, indexA, xorOffset, countsX) {
    TRACE('trick_some_xor; X^A,X|B => A->B, X leaf');
    var offset1 = bounty_getOffset(bounty, indexX, 0);
    var offset2 = bounty_getOffset(bounty, indexX, 1);
    var someOffset = offset1 === xorOffset ? offset2 : offset1;
    TRACE(' - xorOffset:', xorOffset, ', someOffset:', someOffset, ', indexX:', indexX, ', metaX:', bounty__debugMeta(bounty, indexA));
    ASSERT(ml_dec16(ml, xorOffset + 1) === 2, 'xors have 2 args');
    ASSERT(countsX === 2, 'x should be part of SOME and XOR');

    if (ml_dec16(ml, someOffset + 1) !== 2) {
      TRACE(' - SOME doesnt have 2 args, bailing');
      return false;
    }

    var X = getDomain(indexX, true);

    if (!domain_isBooly(X)) {
      TRACE(' - X is not a booly, this should be solved by minimizer, bailing');
      requestAnotherCycle = true;
      return false;
    }

    ASSERT(readIndex(ml, someOffset + OFFSET_C_A) === indexX || readIndex(ml, someOffset + OFFSET_C_B) === indexX);
    var indexB = readIndex(ml, someOffset + OFFSET_C_A);
    if (indexB === indexX) indexB = readIndex(ml, someOffset + OFFSET_C_B);
    TRACE(' - indexes: X=', indexX, ', A=', indexA, ', B=', indexB);
    TRACE(' - domains: X=', domain__debug(getDomain(indexX)), ', A=', domain__debug(getDomain(indexA)), ', B=', domain__debug(getDomain(indexB)));
    TRACE_MORPH('X ^ A, X | B', 'A -> B');
    TRACE(' - indexes: A=', indexA, ', B=', indexB, ', X=', indexX);
    TRACE(' - domains: A=', domain__debug(getDomain(indexA)), ', B=', domain__debug(getDomain(indexB)), ', X=', domain__debug(getDomain(indexX))); // We dont have to bother with booly checks since there are two occurrences of X left and they both concern booly ops

    solveStack.push(function (_, force, getDomain, setDomain) {
      TRACE('trick_some_xor');
      var A = getDomain(indexA);
      var B = getDomain(indexB);
      var X = getDomain(indexX);
      TRACE(' - X ^ A, X | B  =>  A -> B');
      TRACE(' - A=', domain__debug(A), ', B=', domain__debug(B), ', X=', domain__debug(X));

      if (domain_isZero(A)) {
        TRACE(' - A=0 so X>0');
        X = domain_removeValue(X, 0);
      } else if (domain_hasNoZero(A)) {
        TRACE(' - A>0 so X=0');
        X = domain_removeGtUnsafe(X, 0);
      } else if (domain_isZero(B)) {
        TRACE(' - B=0 so X>0');
        X = domain_removeValue(X, 0);
      } else {
        TRACE(' - A is booly and B>0 so force A and solve X accordingly');

        if (force(indexA) === 0) {
          TRACE(' - A=0 so X>0');
          X = domain_removeValue(X, 0);
        } else {
          TRACE(' - A>0 so X=0');
          X = domain_removeGtUnsafe(X, 0);
        }
      }

      setDomain(indexX, X);
      ASSERT(getDomain(indexA) && !domain_isBooly(getDomain(indexA)));
      ASSERT(getDomain(indexB));
      ASSERT(getDomain(indexX) && !domain_isBooly(getDomain(indexX)));
      ASSERT(domain_isZero(getDomain(indexA)) !== domain_isZero(getDomain(indexX)));
      ASSERT(!domain_hasZero(getDomain(indexX)) || !domain_hasZero(getDomain(indexB)));
    });
    ml_eliminate(ml, someOffset, SIZEOF_C_2);
    ml_c2c2(ml, xorOffset, 2, ML_IMP, indexA, indexB);
    bounty_markVar(bounty, indexA);
    bounty_markVar(bounty, indexB);
    bounty_markVar(bounty, indexX);
    somethingChanged();
    return true;
  }

  function trickNallOnly(indexX, countsX) {
    TRACE('trickNallOnly;', indexX, ', counts:', countsX);

    if (countsX >= BOUNTY_MAX_OFFSETS_TO_TRACK) {
      TRACE(' - counts (', countsX, ') is higher than max number of offsets we track so we bail on this trick');
      return false;
    }

    var X = getDomain(indexX, true);

    if (domain_isZero(X)) {
      TRACE(' - X has is zero so NALL is already solved, rerouting to minimizer');
      requestAnotherCycle = true;
      return false;
    }

    if (domain_hasNoZero(X)) {
      TRACE(' - X has has no zero should be removed from NALL, rerouting to minimizer');
      requestAnotherCycle = true;
      return false;
    }

    TRACE(' - X contains zero and is only part of nalls, leaf X and eliminate the nalls');
    var offsets = []; // To eliminate

    var indexes = []; // To mark and to defer solve

    for (var i = 0; i < countsX; ++i) {
      var offset = bounty_getOffset(bounty, indexX, i);
      ASSERT(offset, 'bounty should assert that there are counts offsets');
      ASSERT(ml_dec8(ml, offset) === ML_NALL, 'bounty should assert that all ops are nalls');
      var argCount = ml_dec16(ml, offset + 1);

      for (var j = 0; j < argCount; ++j) {
        var index = readIndex(ml, offset + SIZEOF_C + j * 2);
        if (index !== indexX) indexes.push(index); // Dont mark here because that may affect the getOffset call above
      } // Let's hope this list doenst grow too much... (but we have to dedupe the indexes!)


      if (offsets.indexOf(offset) < 0) offsets.push(offset);
    }

    TRACE(' - collected offsets and vars:', offsets, indexes); // TODO: we can improve this step and prevent some force solvings

    TRACE(' - solving X to 0 now to simplify everything');

    if (!domain_isZero(X)) {
      ASSERT(domain_hasZero(X), 'checked above');
      setDomain(indexX, domain_createValue(0));
    }

    TRACE(' - now remove these nalls:', offsets);

    for (var _i28 = 0, len = offsets.length; _i28 < len; ++_i28) {
      var _offset12 = offsets[_i28];
      TRACE_MORPH('nall(X...)', '', 'leaf a nall arg that is only used in nalls');

      var _argCount7 = ml_dec16(ml, _offset12 + 1);

      var opSize = SIZEOF_C + _argCount7 * 2;
      TRACE('   - argcount=', _argCount7, ', opSize=', opSize);
      ml_eliminate(ml, _offset12, opSize);
    }

    for (var _i29 = 0, _len9 = indexes.length; _i29 < _len9; ++_i29) {
      var indexY = indexes[_i29];
      bounty_markVar(bounty, indexY);
    }

    bounty_markVar(bounty, indexX);
    somethingChanged();
    return true;
  }

  function trickSomeOnly(indexX, countsX) {
    TRACE('trickSomeOnly;', indexX, ', counts:', countsX);

    if (countsX >= BOUNTY_MAX_OFFSETS_TO_TRACK) {
      TRACE(' - counts (', countsX, ') is higher than max number of offsets we track so we bail on this trick');
      return false;
    }

    var X = getDomain(indexX, true);

    if (domain_hasNoZero(X)) {
      TRACE(' - X has no zero so SOME is already solved, rerouting to minimizer');
      requestAnotherCycle = true;
      return false;
    }

    if (domain_isZero(X)) {
      TRACE(' - X has is zero so should be removed from this SOME, rerouting to minimizer');
      requestAnotherCycle = true;
      return false;
    }

    TRACE(' - X contains a nonzero and is only part of SOMEs, leaf X and eliminate the SOMEs');
    var offsets = []; // To eliminate

    var indexes = []; // To mark and to defer solve

    for (var i = 0; i < countsX; ++i) {
      var offset = bounty_getOffset(bounty, indexX, i);
      ASSERT(offset, 'bounty should assert that there are counts offsets');
      ASSERT(ml_dec8(ml, offset) === ML_SOME, 'bounty should assert that all ops are SOMEs');
      var argCount = ml_dec16(ml, offset + 1);

      for (var j = 0; j < argCount; ++j) {
        var index = readIndex(ml, offset + SIZEOF_C + j * 2);
        if (index !== indexX) indexes.push(index); // Dont mark here because that may affect the getOffset call above
      } // Let's hope this list doenst grow too much... (but we have to dedupe the indexes!)


      if (offsets.indexOf(offset) < 0) offsets.push(offset);
    }

    TRACE(' - collected offsets and vars:', offsets, indexes); // TODO: we can improve this step and prevent some force solvings

    TRACE(' - removing 0 from X now to simplify everything');

    if (domain_hasZero(X)) {
      ASSERT(domain_isBooly(X), 'checked above');
      setDomain(indexX, X = domain_removeValue(X, 0));
    }

    TRACE(' - now remove these SOMEs:', offsets);

    for (var _i30 = 0, len = offsets.length; _i30 < len; ++_i30) {
      var _offset13 = offsets[_i30];
      TRACE_MORPH('some(X...)', '', 'leaf a SOME arg that is only used in SOMEs');

      var _argCount8 = ml_dec16(ml, _offset13 + 1);

      var opSize = SIZEOF_C + _argCount8 * 2;
      TRACE('   - argcount=', _argCount8, ', opSize=', opSize);
      ml_eliminate(ml, _offset13, opSize);
    }

    for (var _i31 = 0, _len10 = indexes.length; _i31 < _len10; ++_i31) {
      var indexY = indexes[_i31];
      bounty_markVar(bounty, indexY);
    }

    bounty_markVar(bounty, indexX);
    somethingChanged();
    return true;
  }

  function trick_ltelhs_nalls_some(indexX, countsX) {
    TRACE('trick_ltelhs_nalls_some; indexX=', indexX);
    TRACE(' - A !& X, X <= B, X | C    ->     B | C, A <= C    (for any number of nall[2] ops)'); // TOFIX: is this bool only?

    if (!domain_isBool(getDomain(indexX))) {
      TRACE(' - X wasnt bool (', domain__debug(getDomain(indexX)), '), bailing');
      return false;
    }

    if (countsX >= BOUNTY_MAX_OFFSETS_TO_TRACK) {
      TRACE(' - counts (', countsX, ') is higher than max number of offsets we track so we bail on this trick');
      return false;
    }

    var lteOffset;
    var someOffset;
    var nallOffsets = [];
    var indexesA = [];
    var indexB;
    var indexC;

    for (var i = 0; i < countsX; ++i) {
      var offset = bounty_getOffset(bounty, indexX, i);
      if (!offset) break;
      var opCode = ml_dec8(ml, offset);
      ASSERT(opCode === ML_NALL || opCode === ML_SOME || opCode === ML_LTE, 'bounty should assert it logged one of these three ops');

      if (ml_dec16(ml, offset + 1) !== 2) {
        TRACE(' - found an op that did not have 2 args, bailing');
        return false;
      }

      var indexL = readIndex(ml, offset + OFFSET_C_A);
      var indexR = readIndex(ml, offset + OFFSET_C_B);
      ASSERT(indexX === indexL || indexX === indexR, 'bounty should assert that x is part of this op');
      var indexY = indexL === indexX ? indexR : indexL;

      if (opCode === ML_NALL) {
        nallOffsets.push(offset);
        indexesA.push(indexY);
      } else if (opCode === ML_SOME) {
        if (someOffset) {
          TRACE(' - trick only supported with one OR, bailing');
          return false;
        }

        someOffset = offset;
        indexC = indexY;
      } else {
        ASSERT(opCode === ML_LTE, 'if not the others then this');

        if (lteOffset) {
          TRACE(' - trick only supported with one LTE, bailing');
          return false;
        }

        lteOffset = offset;
        indexB = indexY;
      }
    }

    TRACE(' - collection complete; or offset:', someOffset, ', indexesA:', indexesA, ', indexB:', indexB, ', indexC:', indexC, ', indexX:', indexX, ', lte offset:', lteOffset, ', nall offsets:', nallOffsets);
    TRACE_MORPH('A !& X, X <= B, X | C', 'B | C, A <= C');
    TRACE_MORPH('A !& X, D !& X, X <= B, X | C', 'B | C, A <= C, D <= C', 'for any nall, all ops have 2 args');
    TRACE('   - every "other" arg of each nall should be <= C');
    ml_c2c2(ml, lteOffset, 2, ML_SOME, indexB, indexC);
    ml_eliminate(ml, someOffset, SIZEOF_C_2);

    for (var _i32 = 0, len = indexesA.length; _i32 < len; ++_i32) {
      var indexA = indexesA[_i32];
      ml_c2c2(ml, nallOffsets[_i32], 2, ML_LTE, indexA, indexC);
      bounty_markVar(bounty, indexA);
    } // Let t = `
    //  ${['   - X!&A, ', indexesA.map(indexA => domain__debug(getDomain(indexX)) + ' !& ' + domain__debug(getDomain(indexA))).join(', ')]}
    //  ${['   - X<=B, ', domain__debug(getDomain(indexX)), '<=', domain__debug(getDomain(indexB))]}
    //  ${['   - X|C,  ', domain__debug(getDomain(indexX)), '|', domain__debug(getDomain(indexC))]}
    // `;


    TRACE('   - X is a leaf var', indexX);
    solveStack.push(function (_, force, getDomain, setDomain) {
      TRACE(' - or+lte+nalls;', indexX);
      TRACE(' - this was `A !& X, X <= B, X | C` with any number of !&');
      TRACE('   - A=', indexesA.map(function (index) {
        return domain__debug(getDomain(index));
      }), ', B=', domain__debug(getDomain(indexB)), ', C=', domain__debug(getDomain(indexC)), ', X=', domain__debug(getDomain(indexX))); // TRACE(t)

      TRACE(' - before:');
      TRACE('   - X!&A, ', indexesA.map(function (indexA) {
        return domain__debug(getDomain(indexX)) + ' !& ' + domain__debug(getDomain(indexA));
      }).join(', '));
      TRACE('   - X<=B, ', domain__debug(getDomain(indexX)), '<=', domain__debug(getDomain(indexB)));
      TRACE('   - X|C,  ', domain__debug(getDomain(indexX)), '|', domain__debug(getDomain(indexC)));
      var B = getDomain(indexB);
      var C = getDomain(indexC);
      var X = getDomain(indexX);
      TRACE(' - first scan whether X should be set or unset');
      var setIt = false;
      var unsetIt = false;

      if (domain_isZero(C)) {
        TRACE(' - C is zero so X must be set');
        setIt = true;
      }

      indexesA.forEach(function (indexA) {
        var A = getDomain(indexA);

        if (domain_hasNoZero(A)) {
          TRACE(' - there was a nall arg that was set so X must be unset');
          unsetIt = true;
        }
      });
      TRACE(' - so; set?', setIt, ', unset?', unsetIt);
      ASSERT(!(setIt && unsetIt));

      if (setIt) {
        X = domain_removeValue(X, 0);
        X = domain_removeGtUnsafe(X, domain_min(B));
        TRACE(' - Set X and applied LTE: X=', domain__debug(X), ', B=', domain__debug(B));
      } else if (unsetIt) {
        X = domain_removeGtUnsafe(X, 0);
        X = domain_removeGtUnsafe(X, domain_min(B));
        TRACE(' - Unsetting X and applied LTE: X=', domain__debug(X), ', B=', domain__debug(B));
      } else {
        X = domain_removeGtUnsafe(X, domain_min(B));
        if (domain_isBooly(X)) X = domain_removeValue(X, 0);
        TRACE(' - first applied LTE and then forced a booly state; X=', domain__debug(X), ', B=', domain__debug(B));
      }

      setDomain(indexX, X);
      TRACE(' - feedback new value of X (', domain__debug(X), ')'); // If X is zero then all the NALLs are already satisfied

      if (domain_hasNoZero(X)) {
        TRACE(' - X>0 so forcing all NALL args to be zero');
        indexesA.forEach(function (indexA) {
          var A = getDomain(indexA);
          A = domain_removeGtUnsafe(A, 0);
          setDomain(indexA, A);
        });
      }

      TRACE(' - Remove any value from B=', domain__debug(B), 'that is below X=', domain__debug(X), ', max(X)=', domain_max(X));
      B = domain_removeLtUnsafe(B, domain_max(X));
      setDomain(indexB, B);
      TRACE(' - if X=0 then C>0, X=', domain__debug(X), ', C=', domain__debug(C));

      if (domain_isZero(X)) {
        C = domain_removeValue(C, 0);
        setDomain(indexC, C);
      }

      TRACE(' - result:');
      TRACE('   - X!&A, ', indexesA.map(function (indexA) {
        return domain__debug(getDomain(indexX)) + ' !& ' + domain__debug(getDomain(indexA));
      }).join(', '));
      TRACE('   - X<=B, ', domain__debug(getDomain(indexX)), '<=', domain__debug(getDomain(indexB)));
      TRACE('   - X|C,  ', domain__debug(getDomain(indexX)), '|', domain__debug(getDomain(indexC)));
      ASSERT(getDomain(indexB));
      ASSERT(getDomain(indexC));
      ASSERT(getDomain(indexX));
      ASSERT(!indexesA.some(function (indexA) {
        return !domain_isZero(getDomain(indexA)) && !domain_isZero(getDomain(indexX));
      }));
      ASSERT(domain_max(getDomain(indexX)) <= domain_min(getDomain(indexX)));
      ASSERT(domain_hasNoZero(getDomain(indexX)) || domain_hasNoZero(getDomain(indexC)));
    });
    bounty_markVar(bounty, indexB);
    bounty_markVar(bounty, indexC);
    bounty_markVar(bounty, indexX);
    somethingChanged();
    return true;
  }

  function trick_implhs_nalls_some(indexX, countsX) {
    TRACE('trick_implhs_nalls_some; indexX=', indexX);
    TRACE(' - A !& X, X -> B, X | C    ->     B | C, A -> C    (for any number of nall[2] ops)'); // TOFIX: is this bool only?

    if (countsX >= BOUNTY_MAX_OFFSETS_TO_TRACK) {
      TRACE(' - counts (', countsX, ') is higher than max number of offsets we track so we bail on this trick');
      return false;
    }

    var impOffset;
    var someOffset;
    var nallOffsets = [];
    var indexesA = [];
    var indexB;
    var indexC;

    for (var i = 0; i < countsX; ++i) {
      var offset = bounty_getOffset(bounty, indexX, i);
      if (!offset) break;
      var opCode = ml_dec8(ml, offset);
      ASSERT(opCode === ML_NALL || opCode === ML_SOME || opCode === ML_IMP, 'bounty should assert it logged one of these three ops');

      if (ml_dec16(ml, offset + 1) !== 2) {
        TRACE(' - found an op that did not have 2 args, bailing');
        return false;
      }

      var indexL = readIndex(ml, offset + OFFSET_C_A);
      var indexR = readIndex(ml, offset + OFFSET_C_B);
      ASSERT(indexX === indexL || indexX === indexR, 'bounty should assert that x is part of this op');
      var indexY = indexL === indexX ? indexR : indexL;

      if (opCode === ML_NALL) {
        nallOffsets.push(offset);
        indexesA.push(indexY);
      } else if (opCode === ML_SOME) {
        if (someOffset) {
          TRACE(' - trick only supported with one OR, bailing');
          return false;
        }

        someOffset = offset;
        indexC = indexY;
      } else {
        ASSERT(opCode === ML_IMP, 'if not the others then this');

        if (impOffset) {
          TRACE(' - trick only supported with one IMP, bailing');
          return false;
        }

        impOffset = offset;
        indexB = indexY;
      }
    }

    TRACE(' - collection complete; or offset:', someOffset, ', indexesA:', indexesA, ', indexB:', indexB, ', indexC:', indexC, ', indexX:', indexX, ', imp offset:', impOffset, ', nall offsets:', nallOffsets);
    TRACE('   - A !& X, X -> B, X | C    ->     B | C, A -> C');
    TRACE('   - A !& X, D !& X, X -> B, X | C    ->     B | C, A -> C, D -> C');
    TRACE('   - every "other" arg of each nall should be -> C');
    ml_c2c2(ml, impOffset, 2, ML_SOME, indexB, indexC);
    ml_eliminate(ml, someOffset, SIZEOF_C_2);

    for (var _i33 = 0, len = indexesA.length; _i33 < len; ++_i33) {
      var indexA = indexesA[_i33];
      ml_c2c2(ml, nallOffsets[_i33], 2, ML_IMP, indexA, indexC);
      bounty_markVar(bounty, indexA);
    }

    TRACE('   - X is a leaf var', indexX);
    solveStack.push(function (_, force, getDomain, setDomain) {
      TRACE(' - imp+nalls+some;', indexX);
      TRACE(' - this was `A !& X, X -> B, X | C` with any number of !&');
      TRACE(' - indexes: A=', indexesA, ', B=', indexB, ', C=', indexC, ', X=', indexX);
      TRACE(' - domains: A=', indexesA.map(function (a) {
        return domain__debug(getDomain(a));
      }), ', B=', domain__debug(getDomain(indexB)), ', C=', domain__debug(getDomain(indexC)), ', X=', domain__debug(getDomain(indexX)));
      var X = getDomain(indexX);
      var nX = X; // A !& X for all A

      if (!domain_isZero(nX)) {
        // If X is 0 then the nall already passes
        for (var _i34 = 0, _len11 = indexesA.length; _i34 < _len11; ++_i34) {
          var _indexA = indexesA[_i34];
          var A = getDomain(_indexA);

          if (domain_hasNoZero(A) || force(_indexA) !== 0) {
            TRACE(' - at least one NALL pair had a nonzero so X must be zero');
            nX = domain_removeGtUnsafe(nX, 0);
            break; // Now each nall will be fulfilled since X is zero
          }
        }
      } // X | C so if C is zero then X must be nonzero


      var C = getDomain(indexC);

      if (domain_isBooly(C)) {
        force(C);
        C = getDomain(indexC);
      }

      if (domain_isZero(C)) {
        TRACE(' - the SOME pair C was zero so X must be nonzero');
        nX = domain_removeValue(nX, 0);
      } // Maintain X -> B


      var B = getDomain(indexB);

      if (domain_isBooly(B)) {
        force(B);
        B = getDomain(indexB);
      }

      if (domain_isZero(B)) {
        TRACE(' - B is zero so X must be zero');
        nX = domain_removeGtUnsafe(nX, 0);
      }

      ASSERT(nX);
      if (X !== nX) setDomain(indexX, nX);
    });
    bounty_markVar(bounty, indexB);
    bounty_markVar(bounty, indexC);
    bounty_markVar(bounty, indexX);
    somethingChanged();
    return true;
  }

  function trick_lteboth_nall_some(indexX, countsX) {
    TRACE('trick_lteboth_nall_some', indexX);
    TRACE(' - A <= X, B | X, C !& X, X <= D     ->     A !& C, B | D, A <= D, C <= B'); // If we can model `A !& C, A <= D` in one constraint then we should do so but I couldn't find one
    // (when more lte's are added, that's the pattern we add for each)
    // TOFIX: is this bool only?
    // we only want exactly four ops here... and if max is set to something lower then this trick has no chance at all

    if (countsX > 4 || countsX >= BOUNTY_MAX_OFFSETS_TO_TRACK) {
      TRACE(' - we need exactly four constraints for this trick but have', countsX, ', bailing');
      return false;
    } // Note: bounty tracks lte_rhs and lte_lhs separate so if we have four constraints
    // here can trust bounty to assert they are all our targets, no more, no less.
    // we should have; LTE_RHS, LTE_LHS, NALL, SOME


    var lteLhsOffset;
    var lteRhsOffset;
    var someOffset;
    var nallOffset;
    var indexA;
    var indexB;
    var indexC;
    var indexD;

    for (var i = 0; i < countsX; ++i) {
      var offset = bounty_getOffset(bounty, indexX, i);
      ASSERT(offset, 'bounty should assert to fetch as many offsets as there are counts');
      var opCode = ml_dec8(ml, offset);
      ASSERT(opCode === ML_NALL || opCode === ML_SOME || opCode === ML_LTE, 'bounty should assert the op is one of these'); // TODO: this kind of breaks on an op with 1 arg

      var indexL = readIndex(ml, offset + OFFSET_C_A);
      var indexR = readIndex(ml, offset + OFFSET_C_B);
      ASSERT(indexX === indexL || indexX === indexR, 'bounty should assert X is one of the args');
      var indexY = indexL === indexX ? indexR : indexL;

      if (opCode === ML_NALL) {
        ASSERT(!nallOffset, 'cant have a second NALL as per bounty');
        indexC = indexY;
        nallOffset = offset;
      } else if (opCode === ML_SOME) {
        ASSERT(!someOffset, 'cant have a second SOME as per bounty');
        indexB = indexY;
        someOffset = offset;
      } else {
        ASSERT(opCode === ML_LTE, 'asserted by bounty see above');

        if (indexL === indexX) {
          // Lte_lhs
          ASSERT(!lteLhsOffset, 'cant have a second lte_lhs');
          lteLhsOffset = offset;
          indexD = indexY;
        } else {
          // Lte_rhs
          ASSERT(indexR === indexX, 'x already asserted to be one of the op args');
          ASSERT(!lteRhsOffset, 'cant have a second lte_rhs');
          lteRhsOffset = offset;
          indexA = indexY;
        }
      }
    }

    TRACE(' - collection complete; offsets:', lteLhsOffset, lteRhsOffset, someOffset, nallOffset, ', indexes: X=', indexX, ', A=', indexA, ', B=', indexB, ', C=', indexC, ', D=', indexD);
    TRACE(' - A <= X, B | X, C !& X, X <= D     ->     A !& C, B | D, A <= D, C <= B');
    ml_c2c2(ml, lteLhsOffset, 2, ML_LTE, indexA, indexD);
    ml_c2c2(ml, lteRhsOffset, 2, ML_LTE, indexC, indexD);
    ml_c2c2(ml, someOffset, 2, ML_SOME, indexB, indexD);
    ml_c2c2(ml, nallOffset, 2, ML_NALL, indexA, indexC);
    TRACE('   - X is a leaf var', indexX);
    solveStack.push(function (_, force, getDomain, setDomain) {
      TRACE(' - some+nall+lte_lhs+lte_rhs;', indexX);
      var X = getDomain(indexX);

      if (force(indexA) === 1) {
        // A<=X so if A is 1, X must also be 1
        X = domain_removeValue(X, 0);
        ASSERT(X, 'X should be able to reflect the solution');
        setDomain(indexX, X);
      } else if (force(indexB) === 0) {
        // X|B so if B is 0, X must be non-zero
        X = domain_removeValue(X, 0);
        ASSERT(X, 'X should be able to reflect the solution');
        setDomain(indexX, X);
      } else if (force(indexC) > 0) {
        // If indexA is set, X must be zero
        X = domain_removeGtUnsafe(X, 0);
        ASSERT(X, 'X should be able to reflect the solution');
        setDomain(indexX, X);
      } else if (force(indexD) === 0) {
        // X<=D, if indexD is 0, X must be zero
        X = domain_removeGtUnsafe(X, 0);
        ASSERT(X, 'X should be able to reflect the solution');
        setDomain(indexX, X);
      }
    });
    bounty_markVar(bounty, indexA);
    bounty_markVar(bounty, indexB);
    bounty_markVar(bounty, indexC);
    bounty_markVar(bounty, indexD);
    bounty_markVar(bounty, indexX);
    somethingChanged();
    return true;
  }

  function trick_impboth_nall_some(indexX, countsX) {
    TRACE('trick_impboth_nall_some', indexX);
    TRACE(' - A -> X, B | X, C !& X, X -> D             =>     A !& C, B | D, A -> D, C -> B'); // We want a NALL[2], SOME[2], IMP_LHS, and one or more IMP_RHS
    // if we can model `A !& C, A -> D` in one constraint then we should do so but I couldn't find one
    // - A->(B<?C)
    // - A==(C&A&!B)
    // - B<C|!A       /       B<C|A==0
    // (when more IMPs are added, we add the same pattern for each)
    // TOFIX: is this bool only?

    if (countsX !== 4 || countsX >= BOUNTY_MAX_OFFSETS_TO_TRACK) {
      TRACE(' - we need 4 constraints for this trick but have', countsX, ', bailing');
      return false;
    } // Note: bounty tracks imp_rhs and imp_lhs separate so if we have four constraints
    // here can trust bounty to assert they are all our targets, no more, no less.
    // TODO: what if somehow X->X ocurred here? (due to other rewrite inside cutter)
    // we should have; 1x IMP_RHS, 1x IMP_LHS, 1x NALL, 1x SOME


    var impLhsOffset;
    var impRhsOffset;
    var someOffset;
    var nallOffset;
    var indexA;
    var indexB;
    var indexC;
    var indexD;

    for (var i = 0; i < countsX; ++i) {
      var offset = bounty_getOffset(bounty, indexX, i);
      ASSERT(offset, 'bounty should assert to fetch as many offsets as there are counts');
      var opCode = ml_dec8(ml, offset);
      ASSERT(opCode === ML_NALL || opCode === ML_SOME || opCode === ML_IMP, 'bounty should assert the op is one of these'); // TODO: this kind of breaks on an op with 1 arg

      var indexL = readIndex(ml, offset + OFFSET_C_A);
      var indexR = readIndex(ml, offset + OFFSET_C_B);
      ASSERT(indexX === indexL || indexX === indexR, 'bounty should assert X is one of the args');

      if (opCode === ML_NALL) {
        ASSERT(nallOffset === undefined, 'bounty said so');
        indexC = indexL === indexX ? indexR : indexL;
        nallOffset = offset;
      } else if (opCode === ML_SOME) {
        ASSERT(someOffset === undefined, 'bounty said so');
        indexB = indexL === indexX ? indexR : indexL;
        someOffset = offset;
      } else {
        ASSERT(opCode === ML_IMP, 'asserted by bounty see above');
        var indexY = indexL === indexX ? indexR : indexL;

        if (indexL === indexX) {
          // Imp_lhs
          ASSERT(impLhsOffset === undefined, 'bounty said so');
          impLhsOffset = offset;
          indexD = indexY;
        } else {
          // Imp_rhs
          ASSERT(indexR === indexX, 'x already asserted to be one of the op args');
          ASSERT(impRhsOffset === undefined, 'bounty said so');
          impRhsOffset = offset;
          indexA = indexY;
        }
      }
    }

    TRACE(' - collection complete; offsets:', impLhsOffset, impRhsOffset, someOffset, nallOffset, ', indexes: X=', indexX, ', A=', indexA, ', B=', indexB, ', C=', indexC, ', D=', indexD);
    TRACE(' - A -> X, B | X, C !& X, X -> D, X -> E     =>     A !& C, B | D, A -> D, C -> B, A -> E, C -> E');

    if (!domain_isBool(getDomain(indexA, true)) || !domain_isBool(getDomain(indexB, true)) || !domain_isBool(getDomain(indexC, true)) || !domain_isBool(getDomain(indexD, true))) {
      TRACE(' - At least one of the domains wasnt a bool, bailing for now');
      return false;
    }

    TRACE_MORPH(' - C !& X, B | X, A -> X, X -> D', ' - A !& C, B | D, A -> D, C -> B');
    ml_c2c2(ml, impLhsOffset, 2, ML_IMP, indexA, indexD);
    ml_c2c2(ml, impRhsOffset, 2, ML_IMP, indexC, indexD);
    ml_c2c2(ml, someOffset, 2, ML_SOME, indexB, indexD);
    ml_c2c2(ml, nallOffset, 2, ML_NALL, indexA, indexC);
    TRACE('   - X is a leaf var', indexX);
    leafs.push(indexX);
    solveStack.push(function (_, force, getDomain, setDomain) {
      TRACE(' - some+nall+imp_lhs+imp_rhs;', indexX); // TODO: we can be less forcing here

      var X = getDomain(indexX);

      if (force(indexA) === 1) {
        // A->X so if A is 1, X must also be 1
        X = domain_removeValue(X, 0);
        ASSERT(X, 'X should be able to reflect the solution');
        setDomain(indexX, X);
      } else if (force(indexB) === 0) {
        // X|B so if B is 0, X must be non-zero
        X = domain_removeValue(X, 0);
        ASSERT(X, 'X should be able to reflect the solution');
        setDomain(indexX, X);
      } else if (force(indexC) > 0) {
        // X!&C so if indexA is set, X must be zero
        X = domain_removeGtUnsafe(X, 0);
        ASSERT(X, 'X should be able to reflect the solution');
        setDomain(indexX, X);
      } else if (force(indexD) === 0) {
        // X->D, if indexD is 0, X must be zero
        X = domain_removeGtUnsafe(X, 0);
        ASSERT(X, 'X should be able to reflect the solution');
        setDomain(indexX, X);
      }
    });
    bounty_markVar(bounty, indexA);
    bounty_markVar(bounty, indexB);
    bounty_markVar(bounty, indexC);
    bounty_markVar(bounty, indexD);
    bounty_markVar(bounty, indexX);
    somethingChanged();
    return true;
  }

  function trick_issame_sum(ml, sumOffset, indexR, counts, argCount, sum, min, max, constantValue, constantArgIndex, allSumArgsBoolyPairs) {
    // Only if all sum args are strict bools ([0 1]), one constant excluded
    // (R = sum(A B C) & (S = R==?3)        ->    S = all?(A B C)
    // (R = sum(A B C) & (S = R==?0)        ->    S = none?(A B C)
    // (R = sum(A B C) & (S = R==?[0 1])    ->    S = nall?(A B C)
    // (R = sum(A B C) & (S = R==?[1 2])    ->    S = some?(A B C)
    // R = sum( ... ), S = R ==? count                       ->   S = all?( ... )
    // R = sum( ... ), S = R ==? 0                           ->   S = none?( ... )
    // R = sum( ... ), S = R ==? [0 0 count-1 count-1]       ->   S = nall?( ... )
    // R = sum( ... ), S = R ==? [1 1 count count]           ->   S = some?( ... )
    // R = sum([0 0 3 3], [0 0 5 5]), S = R ==? 8            ->   S = all?( ... )
    // R = sum( ... ), S = R ==? sum-max-args                ->   S = all?( ... )
    var offset1 = bounty_getOffset(bounty, indexR, 0);
    var offset2 = bounty_getOffset(bounty, indexR, 1);
    var issameOffset = offset1 === sumOffset ? offset2 : offset1;
    TRACE('trick_issame_sum; sumOffset:', sumOffset, ', issameOffset:', issameOffset, ', indexR:', indexR, ', countsR:', counts, ', metaR:', bounty__debugMeta(bounty, indexR), ', min:', min, ', max:', max, ', const:', constantValue, ', const arg pos:', constantArgIndex);
    ASSERT(min >= 0 && max >= 0 && min <= max, 'min/max check');
    ASSERT(constantValue >= 0, 'constant value should be positive or zero');
    ASSERT(issameOffset > 0, 'offset should exist and cant be the first op');
    ASSERT(counts === 2, 'R should only be used in two constraints (sum and issame)');
    ASSERT(getMeta(bounty, indexR) === (BOUNTY_FLAG_ISSAME_ARG | BOUNTY_FLAG_SUM_RESULT), 'should be sum and issame arg', counts, bounty__debugMeta(bounty, indexR));
    ASSERT(ml_dec8(ml, sumOffset) === ML_SUM, 'check sum offset');
    ASSERT(ml_dec8(ml, issameOffset) === ML_ISSAME, 'check issame offset');
    ASSERT(ml_dec16(ml, sumOffset + 1) === argCount, 'argcount should match');
    ASSERT(constantArgIndex < argCount, 'should be valid const pos');
    var issameArgCount = ml_dec16(ml, issameOffset + 1);

    if (issameArgCount !== 2) {
      TRACE(' - issame does not have 2 args, bailing for now');
      return false;
    } // S = R ==? X


    var indexA = readIndex(ml, issameOffset + OFFSET_C_A); // R or X

    var indexB = readIndex(ml, issameOffset + OFFSET_C_B); // R or X

    var indexS = readIndex(ml, issameOffset + OFFSET_C_R); // S

    ASSERT(indexA === indexR || indexB === indexR, 'R should be an arg of the issame');
    var indexX = indexA;
    if (indexX === indexR) indexX = indexB;
    TRACE(' - S = R ==? X; indexes=', indexS, '=', indexR, '==?', indexX);
    TRACE(' - ', domain__debug(getDomain(indexS)), '=', domain__debug(getDomain(indexR)), '==?', domain__debug(getDomain(indexX)));
    var R = getDomain(indexR, true);
    var X = getDomain(indexX, true);
    var vX = domain_getValue(X);

    if (vX >= 0 && !domain_containsValue(R, vX)) {
      // This case should be handled by the minimizer but deduper/earlier cutter steps could lead to it here anyways
      // bailing so minimizer can take care of it in the next cycle
      TRACE(' - R didnt contain B so unsafe for leaf cutting, bailing');
      requestAnotherCycle = true;
      return false;
    } // Let want = domain_createRange(min, max);


    var Rwant = domain_intersection(R, sum);
    TRACE(' - R must contain all values in between;', domain__debug(R), 'and', domain__debug(sum), '=', domain__debug(Rwant), '(', sum === Rwant, ')');

    if (Rwant !== sum) {
      TRACE(' - R cant represent all values of the sum'); // , are the args booly pairs?', allSumArgsBoolyPairs, ', vX:', vX, ', max:', max);

      return false;
    }

    TRACE(' - sum R range change check passed'); // Check the case where all the args are boolyPairs and R contains the sum of maxes

    if (allSumArgsBoolyPairs && vX === max) {
      // R = sum([0 0 3 3], [0 0 5 5]), S = R ==? 8            ->   S = all?( ... )
      // R = sum( ... ), S = R ==? sum-max-args                ->   S = all?( ... )
      TRACE(' - all sum args are booly and vX is the sum of maxes, morph to isall');
      TRACE_MORPH('R = sum( ... ), S = R ==? sum-max-args', 'S = all?( ... )');
      ml_enc8(ml, sumOffset, ML_ISALL);
      return _trick_issame_sum_tail(sumOffset, issameOffset, argCount, indexR, indexS, indexX, constantValue, constantArgIndex);
    }

    if (vX >= 0) {
      return _trick_issame_sum_constant(ml, sumOffset, argCount, indexR, issameOffset, indexS, indexX, vX, max, constantValue, constantArgIndex);
    }

    return _trick_issame_sum_domain(ml, sumOffset, argCount, indexR, issameOffset, indexS, indexX, X, constantValue, constantArgIndex);
  }

  function _trick_issame_sum_constant(ml, sumOffset, argCount, indexR, issameOffset, indexS, indexX, vX, max, constantValue, constantArgIndex) {
    TRACE(' - _trick_issame_sum_constant', vX); // This is when the X of S=R==?X is a constant
    // R = sum(A B C), S = R ==? 0          "are none of ABC set"
    // R = sum(A B C 5), S = R ==? 0        S=0 because R is always at least 5. we ignore this here
    // R = sum(A B C 5), S = R ==? 5        "are none of ABC set"
    // R = sum(A B C), S = R ==? 3          "are all args set"
    // R = sum(A B C 5), S = R ==? 3        S=0 because R is always at least 5. we ignore this here
    // R = sum(A B C 5), S = R ==? 8        "are all args set"
    // note: we're not checking the sum bounds here (R is not a leaf). we only want to know how
    // the sum bounds relate to X of the issame.

    TRACE(' - vX=', vX, ', constantValue=', constantValue, ', const arg pos:', constantArgIndex, ', argCount=', argCount, ', for isnone, vX must be', constantValue, ', for isall vX must be', argCount + (constantValue ? constantValue - 1 : 0));
    ASSERT(constantArgIndex < argCount, 'const pos should be valid');
    ASSERT(ml_dec16(ml, issameOffset + 1) === 2, 'issame should have 2 args'); // To remind you; all sum args are at least booly and there is at most one constant among them

    if (vX === constantValue) {
      // This means all non-constant args must become zero
      // for example; R=sum(A,B,C,3,8),S=R==?11 => A=B=C=0
      TRACE(' - min=X so all non-constants must be set to zero to satisfy the sum+issame. that means morph to isnone');
      TRACE_MORPH('R=sum(A,B,C,x,y),S=R==?(x+y)', 'A=B=C=0'); // Sum will fit isnone. it'll be exactly the same size
      // only need to update the op code and the result index, as the rest remains the same

      ml_enc8(ml, sumOffset, ML_ISNONE);
    } else if (vX === max) {
      // This means all non-constant args must be non-zero
      // for example: R=sum(A:[0 1],B:[0 0 2 2],C:[0 1],3,8),S=R==?15 => S=all?(A B C)
      TRACE(' - (c+a-1)==X so all non-constants must be set to non-zero to satisfy the sum+issame. that means morph to isall');
      TRACE_MORPH('R=sum(A:boolypair,B:boolypair,...,y,z,...),S=R==?(max(A)+max(B)+x+y+...)', 'S=all?(A B C ...)'); // Sum will fit isall. it'll be exactly the same size
      // only need to update the op code and the result index, as the rest remains the same

      ml_enc8(ml, sumOffset, ML_ISALL);
    } else {
      TRACE(' - min < X < max, cant morph this, bailing');
      return false;
    }

    return _trick_issame_sum_tail(sumOffset, issameOffset, argCount, indexR, indexS, indexX, constantValue, constantArgIndex);
  }

  function _trick_issame_sum_domain(ml, sumOffset, argCount, indexR, issameOffset, indexS, indexX, X, constantValue, constantArgIndex) {
    TRACE(' - _trick_issame_sum_domain', domain__debug(X)); // This is when the X of S=R==?X is an unsolved domain
    // R = sum(A B C), S = R ==? [0 2]      "are not all of ABC set"
    // R = sum(A B C 5), S = R ==? [0 2]    S=0 because R is always at least 5. we ignore this here
    // R = sum(A B C 5), S = R ==? [5 7]    "are not all of ABC set"
    // R = sum(A B C), S = R ==? [1 3]      "are some of ABC set"
    // R = sum(A B C 5), S = R ==? [1 3]    S=0 because R is always at least 5. we ignore this here
    // R = sum(A B C 5), S = R ==? [6 8]    "are some of ABC set"
    // note: we're not checking the sum bounds here (R is not a leaf). we only want to know how
    // the sum bounds relate to X of the issame.

    TRACE(' - n=', argCount, ', c=', constantValue, '; X=', domain__debug(X), ', issome means [c+1 c+n-1] so [', constantValue + 1, ',', constantValue + argCount - 1, '], and isnall means [c (c-(C?1:0))+n-1] so [', constantValue, ',', constantValue - (constantValue ? 1 : 0) + (argCount - 1), ']');
    ASSERT(ml_dec16(ml, issameOffset + 1) === 2, 'issame should have 2 args');

    if (X === domain_createRange(constantValue + 1, constantValue + argCount - (constantValue ? 1 : 0))) {
      TRACE(' - X requires at least one var to be set, so issome');
      TRACE_MORPH('R = sum(A:bool B:bool C:bool), S = R ==? [1 3]', 'S = some?(A B C)');
      ml_enc8(ml, sumOffset, ML_ISSOME);
    } else if (X === domain_createRange(constantValue, constantValue - (constantValue ? 1 : 0) + (argCount - 1))) {
      TRACE(' - X requires one var to be unset, so isnall');
      TRACE_MORPH('R = sum(A:bool B:bool C:bool), S = R ==? [0 2]', 'S = nall?(A B C)');
      ml_enc8(ml, sumOffset, ML_ISNALL);
    } else {
      TRACE(' - sum bounds does not match X in a useful way, bailing');
      return false;
    }

    return _trick_issame_sum_tail(sumOffset, issameOffset, argCount, indexR, indexS, indexX, constantValue, constantArgIndex);
  }

  function _trick_issame_sum_tail(sumOffset, issameOffset, argCount, indexR, indexS, indexX, constantValue, constantArgIndex) {
    // Note: NO bailing here
    TRACE(' - _trick_issame_sum_tail');
    ASSERT(ml_dec16(ml, issameOffset + 1) === 2, 'issame should have 2 args');
    var newArgCount = removeOneConstantFromArgs(constantValue, constantArgIndex, argCount, sumOffset); // Make S the result var for the isnall/issome/isnone/isall

    ml_enc16(ml, sumOffset + SIZEOF_C + newArgCount * 2, indexS);
    TRACE(' - eliminating the issame, marking all affected vars');
    var args = markAndCollectArgs(ml, sumOffset, newArgCount); // (R = sum(A B C) & (S = R==?3)        ->    S = all?(A B C)
    // (R = sum(A B C) & (S = R==?0)        ->    S = none?(A B C)
    // (R = sum(A B C) & (S = R==?[0 1])    ->    S = nall?(A B C)
    // (R = sum(A B C) & (S = R==?[1 2])    ->    S = some?(A B C)

    solveStack.push(function (_, force, getDomain, setDomain) {
      TRACE(' - _trick_issame_sum_tail; force solving the issame (only)'); // Note: the sum is handled through addSumToSolveStack, which should resolve before this solvestack entry

      var S = getDomain(indexS);
      var R = getDomain(indexR);
      var X = getDomain(indexX);
      ASSERT(domain_isSolved(R), 'this should be solved by the solvestack compiled after this one (addSumToSolveStack)');
      TRACE(' - before: S=', domain__debug(S), ' = R=', domain__debug(R), ' ==? X=', domain__debug(X));

      if (!domain_isBooly(S)) {
        if (!domain_intersection(R, X)) {
          TRACE(' R and X dont intersect so S is falsy');
          S = domain_removeGtUnsafe(S, 0);
          setDomain(indexS, S);
        } else {
          force(indexX);
          X = getDomain(indexX); // Note: R should be solved here

          if (R === X) {
            TRACE(' - X==R so set S to truthy');
            S = domain_removeValue(S, 0);
            setDomain(indexS, S);
          } else {
            TRACE(' - X!=R so set S to falsy');
            S = domain_removeGtUnsafe(S, 0);
            setDomain(indexS, S);
          }
        }
      }

      TRACE(' - between: S=', domain__debug(S), ' = R=', domain__debug(R), ' ==? X=', domain__debug(X));
      ASSERT(!domain_isBooly(S));

      if (domain_isZero(S)) {
        TRACE(' - S=0 so X != R');
        X = domain_removeValue(X, domain_getValue(R));
      } else {
        TRACE(' - S>0 so X == R');
        X = domain_intersection(X, R);
      }

      setDomain(indexX, X);
      TRACE(' - after: S=', domain__debug(S), ' = R=', domain__debug(R), ' ==? X=', domain__debug(X));
      ASSERT(getDomain(indexS));
      ASSERT(getDomain(indexX));
      ASSERT(getDomain(indexR), 'enforced by other solve stack');
      ASSERT(!domain_isBooly(getDomain(indexS)));
      ASSERT(domain_isSolved(getDomain(indexR)), 'the sum result should also be solved (enforced by other solve stack)');
      ASSERT(domain_isZero(getDomain(indexS)) || domain_isSolved(getDomain(indexX)), 'if S>0 then X must be solved to guarantee the eq');
      ASSERT(domain_isZero(getDomain(indexS)) === !domain_intersection(getDomain(indexR), getDomain(indexX)));
    });
    addSumToSolveStack(indexR, args, constantValue);
    ml_eliminate(ml, issameOffset, SIZEOF_CR_2);
    ASSERT(newArgCount === args.length);
    bounty_markVar(bounty, indexS);
    bounty_markVar(bounty, indexR);
    bounty_markVar(bounty, indexX);
    somethingChanged();
    return true;
  }

  function trick_islte_sum(ml, sumOffset, indexR, counts, argCount, min, max, constantValue, constantArgIndex) {
    // Only if all sum args are strict bools ([0 1]), one constant excluded
    // (R = sum(A B C) & (S = R<=?0)        ->    S = none?(A B C)
    // (R = sum(A B C) & (S = R<=?2)        ->    S = nall?(A B C)
    // (R = sum(A B C) & (S = 1<=?R)        ->    S = some?(A B C)
    // (R = sum(A B C) & (S = 3<=?R)        ->    S = all?(A B C)
    // R = sum( ... ), S = R <=? 0          ->    S = none?( ... )
    // R = sum( ... ), S = R <=? count-1    ->    S = nall?( ... )
    // R = sum( ... ), S = 1 <=? R          ->    S = some?( ... )
    // R = sum( ... ), S = count <=? R      ->    S = all?( ... )
    var offset1 = bounty_getOffset(bounty, indexR, 0);
    var offset2 = bounty_getOffset(bounty, indexR, 1);
    var islteOffset = offset1 === sumOffset ? offset2 : offset1;
    TRACE('trick_islte_sum; sumOffset:', sumOffset, ', islteOffset:', islteOffset, ', indexR:', indexR, ', countsR:', counts, ', metaR:', bounty__debugMeta(bounty, indexR), ', min=', min, ', max=', max, ', constantValue=', constantValue);
    ASSERT(islteOffset > 0, 'offset should exist and cant be the first op');
    ASSERT(counts === 2, 'R should only be used in two constraints (sum and islte)');
    ASSERT(getMeta(bounty, indexR) === (BOUNTY_FLAG_ISLTE_ARG | BOUNTY_FLAG_SUM_RESULT), 'should be sum and islte arg', counts, bounty__debugMeta(bounty, indexR));
    ASSERT(ml_dec8(ml, sumOffset) === ML_SUM, 'check sum offset');
    ASSERT(ml_dec8(ml, islteOffset) === ML_ISLTE, 'check islte offset');
    ASSERT(ml_dec16(ml, sumOffset + 1) === argCount, 'argcount should match');
    var indexA = readIndex(ml, islteOffset + 1); // R or ?

    var indexB = readIndex(ml, islteOffset + 3); // R or ?

    var indexS = readIndex(ml, islteOffset + 5); // S

    ASSERT(indexA === indexR || indexB === indexR, 'R should be an arg of the islte');
    var indexX = indexA;
    if (indexX === indexR) indexX = indexB; // (R = sum(...) & (S = A<=?B)
    // (R = sum(...) & (S = R<=?X) or
    // (R = sum(...) & (S = X<=?R)

    var X = getDomain(indexX, true);
    var vX = domain_getValue(X); // We cant check 0 1 n-1 n here because a constant could affect those values. so only check whether X is solved.

    if (vX < 0) {
      TRACE(' - X is not solved, bailing');
      return false;
    }

    var R = getDomain(indexR, true);

    if (!domain_containsValue(R, vX)) {
      // This case should be handled by the minimizer but deduper/earlier cutter steps could lead to it here anyways
      // bailing so minimizer can take care of it in the next cycle
      TRACE(' - R didnt contain B so unsafe for leaf cutting, bailing');
      requestAnotherCycle = true;
      return false;
    }

    TRACE(' - validating sum args now');
    var want = domain_createRange(min, max);
    var Rwant = domain_intersection(R, want);
    TRACE(' - sum args summed; min is', min, 'and max is', max, ', R must contain all values in between;', domain__debug(R), 'and', domain__debug(want), '=', domain__debug(Rwant), '(', Rwant === want, ')');

    if (Rwant !== want) {
      TRACE(' - R cant represent all values of the sum so bailing');
      return false;
    } // Note: we're not checking the sum bounds here (R is not a leaf). we only want to know how
    // the sum bounds relate to X of the islte.
    // the position of R in the isLte determines what values we care about here
    // R = sum( ... ), S = R <=? 0          =>    S = none?( ... )
    // R = sum( ... ), S = R <=? count-1    =>    S = nall?( ... )
    // R = sum( ... ), S = 1 <=? R          =>    S = some?( ... )
    // R = sum( ... ), S = count <=? R      =>    S = all?( ... )


    var targetOp = 0;

    if (indexA === indexR) {
      ASSERT(indexB === indexX);
      TRACE(' - X=', vX, ', n=', argCount, ', c=', constantValue, ', x is to the right. we care about 0 and n-1 (', constantValue, 'and', constantValue - (constantValue ? 1 : 0) + (argCount - 1), ')'); // R = sum(A B C), S = R <=? 0          "are none of ABC set"
      // R = sum(A B C 5), S = R <=? 0        S=0 because R is always at least 5. we ignore this here
      // R = sum(A B C 5), S = R <=? 5        "are non of ABC set"
      // R = sum(A B C), S = R <=? 2          "are at most 2 of ABC set"
      // R = sum(A B C 5), S = R <=? 2        S=0 because R is always at least 5. we ignore this here
      // R = sum(A B C 5), S = R <=? 7        "are at most 2 of ABC set"

      if (vX === constantValue) {
        //
        TRACE(' - this is "are none of the sum args set, ignoring the constant"');
        TRACE_MORPH('R = sum(A B C ...), S = R <=? 0', 'S = none?(A B C ...)');
        targetOp = ML_ISNONE;
      } else if (vX === constantValue - (constantValue ? 1 : 0) + (argCount - 1)) {
        TRACE(' - this is "are not all of the sum args set, ignoring the constant"');
        TRACE_MORPH('R = sum( ... ), S = R <=? count-1', 'S = nall?( ... )');
        targetOp = ML_ISNALL;
      } else {
        TRACE(' - Unable to apply trick, bailing');
        return false;
      }
    } else {
      ASSERT(indexA === indexX && indexB === indexR);
      TRACE(' - X=', vX, ', n=', argCount, ', c=', constantValue, ', x is to the left. we care about 1 and n (', constantValue + 1, 'and', constantValue - (constantValue ? 1 : 0) + argCount, ')'); // R = sum(A B C), S = 1 <= R          "are some of ABC set"
      // R = sum(A B C 5), S = 1 <=? R        S=1 because R is always at least 5. we ignore this here
      // R = sum(A B C 5), S = 6 <=? R        "are some of ABC set"
      // R = sum(A B C), S = 3 <=? R          "are all of ABC set"
      // R = sum(A B C 5), S = 4 <=? R        S=1 because R is always at least 5. we ignore this here
      // R = sum(A B C 5), S = 5+4-1 <=? R    "are all of ABC set"

      if (vX === constantValue + 1) {
        TRACE(' - this is "is at least one sum arg set"');
        TRACE('R = sum( ... ), S = 1 <=? R', 'S = some?( ... )');
        targetOp = ML_ISSOME;
      } else if (vX === constantValue - (constantValue ? 1 : 0) + argCount) {
        TRACE(' - this is "are all of the sum args set"');
        TRACE('R = sum( ... ), S = count <=? R', 'S = all?( ... )');
        targetOp = ML_ISALL;
      } else {
        TRACE(' - Unable to apply trick, bailing');
        return false;
      }
    }

    ASSERT(targetOp !== 0, 'should be one of the four reifier ops'); // NOW update the op. we won't bail after this point.

    ml_enc8(ml, sumOffset, targetOp);
    TRACE(' - eliminating the islte, marking all affected vars');
    TRACE(' - constant value:', constantValue, ', arg index:', constantArgIndex);
    var newArgCount = removeOneConstantFromArgs(constantValue, constantArgIndex, argCount, sumOffset);
    var args = markAndCollectArgs(ml, sumOffset, newArgCount); // The position of R in the isLte determines what values we care about here
    // R = sum( ... ), S = R <=? 0          =>    S = none?( ... )
    // R = sum( ... ), S = R <=? count-1    =>    S = nall?( ... )
    // R = sum( ... ), S = 1 <=? R          =>    S = some?( ... )
    // R = sum( ... ), S = count <=? R      =>    S = all?( ... )
    // make S the result var for the reifier

    ml_enc16(ml, sumOffset + SIZEOF_C + newArgCount * 2, indexS);
    solveStack.push(function (_, force, getDomain, setDomain) {
      TRACE(' - trick_islte_sum; force solving S (only)'); // Note: the sum is handled through addSumToSolveStack, which should resolve before this solvestack entry

      var S = getDomain(indexS);
      var R = getDomain(indexR);
      ASSERT(domain_isSolved(R), 'this should be solved by the solvestack compiled after this one (addSumToSolveStack)');
      TRACE(' - before: S=', domain__debug(S), ', R=', domain__debug(R), ', vX=', vX, ', x left?', indexA === indexX);

      if (!domain_isBooly(S)) {
        if (indexX === indexA) {
          // S = x <= R
          if (vX <= domain_min(R)) {
            TRACE(' - x<=R so set S to truthy');
            S = domain_removeValue(S, 0);
            setDomain(indexS, S);
          } else {
            TRACE(' - R>x so set S to falsy');
            S = domain_removeGtUnsafe(S, 0);
            setDomain(indexS, S);
          }
        } else {
          // S = R <= x
          if (domain_max(R) <= vX) {
            TRACE(' - R<=x so set S to truthy');
            S = domain_removeValue(S, 0);
            setDomain(indexS, S);
          } else {
            TRACE(' - R>x so set S to falsy');
            S = domain_removeGtUnsafe(S, 0);
            setDomain(indexS, S);
          }
        }
      }

      TRACE(' - after: S=', domain__debug(getDomain(indexS)), ', R=', domain__debug(getDomain(indexR)), ', X=', domain__debug(getDomain(indexX)));
      ASSERT(getDomain(indexS));
      ASSERT(getDomain(indexR), 'enforced by other solve stack');
      ASSERT(args.every(getDomain));
      ASSERT(!domain_isBooly(getDomain(indexS)));
      ASSERT(domain_isSolved(getDomain(indexR)), 'the sum result should also be solved (enforced by other solve stack)');
      ASSERT(domain_isZero(getDomain(indexS)) !== (indexX === indexA ? vX <= domain_min(getDomain(indexR)) : domain_max(getDomain(indexR)) <= vX), 'S=x<=R or S=R<=x should hold');
    });
    addSumToSolveStack(indexR, args, constantValue);
    ml_eliminate(ml, islteOffset, SIZEOF_VVV);
    bounty_markVar(bounty, indexR);
    somethingChanged();
    return true;
  }

  function trick_xnor_pseudoSame(ml, offset, indexA, boolyA, indexB, boolyB) {
    // A or B or both are only used as a boolean (in the zero-nonzero sense, not strictly 0,1)
    // the xnor basically says that if one is zero the other one is too, and otherwise neither is zero
    // cominbing that with the knowledge that both vars are only used for zero-nonzero, one can be
    // considered a pseudo-alias for the other. we replace it with the other var and defer solving it.
    // when possible, pick a strictly boolean domain because it's more likely to allow new tricks.
    // note that for a booly, the actual value is irrelevant. whether it's 1 or 5, the ops will normalize
    // this to zero and non-zero anyways. and by assertion the actual value is not used inside the problem
    TRACE(' - trick_xnor_pseudoSame; found booly-eq in a xnor:', indexA, '!^', indexB, ', A booly?', boolyA, ', B booly?', boolyB);
    ASSERT(boolyA || boolyB, 'at least one of the args should be a real booly (as reported by bounty)');
    ASSERT(ml_dec16(ml, offset + 1) === 2, 'should have 2 args'); // Ok, a little tricky, but we're going to consider the bool to be a full alias of the other var.
    // once we create a solution we will override the value and apply the booly constraint and assign
    // it either its zero or nonzero value(s) depending on the other value of this xnor.

    var indexEliminate = indexB; // Eliminate

    var indexKeep = indexA; // Keep
    // keep the non-bool if possible

    if (!boolyB) {
      TRACE(' - keeping B instead because its not a booly');
      indexEliminate = indexA;
      indexKeep = indexB;
    }

    cutAddPseudoBoolyAlias(indexKeep, indexEliminate);
    ml_eliminate(ml, offset, SIZEOF_C_2);
    bounty_markVar(bounty, indexA);
    bounty_markVar(bounty, indexB);
    somethingChanged();
  }

  function trick_sum_booly(ml, sumOffset, indexR, countsR, sum, argCount) {
    // R is used as a result var for a sum
    // we must first confirm that R is a booly (only used as arg in booly places of ops), except for being a sum-result
    // in that case the sum is an isSome because that's the only thing that matters for R
    // note that the meta flags will claim non-booly because (at least) R is the sum result var so we gotta confirm that
    TRACE('trick_sum_booly; sumOffset:', sumOffset, ', indexR:', indexR, ', countsR:', countsR, ', argCount:', argCount, ', metaR:', bounty__debugMeta(bounty, indexR));
    ASSERT((getMeta(bounty, indexR) & BOUNTY_FLAG_SUM_RESULT) === BOUNTY_FLAG_SUM_RESULT, 'shouldve been confirmed');
    ASSERT(ml_dec16(ml, sumOffset + 1) === argCount, 'argcount should match');
    var R = getDomain(indexR, true);
    TRACE(' - first checking whether R (', domain__debug(R), ') is a booly when not counting this sum (pair?', domain_isBoolyPair(R), ')');

    if (!domain_isBoolyPair(R)) {
      // If a var only has a zero and one nonzero value it doesnt matter: it's always booly
      for (var i = 0; i < countsR; ++i) {
        var offset = bounty_getOffset(bounty, indexR, i);
        ASSERT(offset, 'should exist');

        if (offset !== sumOffset) {
          var opCode = ml_dec8(ml, offset);
          var isBooly = cut_isBoolyOp(opCode, true, ml, offset, indexR);

          if (isBooly === ML_BOOLY_NO) {
            TRACE(' - R is at least a non-booly in one op (' + ml__opName(opCode) + '), bailing');
            return;
          }

          ASSERT(isBooly === ML_BOOLY_YES, 'cannot be maybe because asked for explicit lookups');
        }
      }
    }

    TRACE(' - ok, R is booly. next confirming that R can represent any valuation of the sum args, total sum of args:', domain__debug(sum), 'R:', domain__debug(R)); // If sum doesnt intersect with domain then there are valuations of the sum-args such that the result is not in R
    // we could theoretically fix that but it'll be too much work and little to show for. so we just bail.

    if (sum !== domain_intersection(R, sum)) {
      TRACE('  - R does not contain all possible sums so we bail');
      return false;
    }

    TRACE('  - R contains all sums so we can morph the sum to an isall');
    var args = markAndCollectArgs(ml, sumOffset, argCount); // So; in the remaining problem R is only used as booly. so we dont care what the actual value is of R, just
    // whether it's zero or non-zero. so it will arbitrarily be set thusly. we'll add a solveStack entry that
    // makes sure R is solved to the sum of whatever the args are solved to.

    var oR = R; // Back up R because the issome may change it irrelevantly

    solveStack.push(function (_, force, getDomain, setDomain) {
      TRACE(' - trick_sum_booly'); // Note: we need to force solve all args to make sure the sum constraint holds

      var vR = 0;

      for (var _i35 = 0; _i35 < argCount; ++_i35) {
        vR += force(args[_i35]);
      }

      var R = domain_intersectionValue(oR, vR);
      ASSERT(R, 'R should be able to reflect the solution');
      if (oR !== R) setDomain(indexR, R, false, true);
    }); // The sum is a count-result-op and so is the isAll so we only need to replace the opcode

    ml_enc8(ml, sumOffset, ML_ISSOME);
    bounty_markVar(bounty, indexR);
    somethingChanged();
    return true;
  }

  function trick_issame_issame_sum(ml, sumOffset, indexR, countsR, sum, argCount) {
    // R = sum(A B), S = R ==? 1, T = R ==? 2    ->    S = A !=? B, T = all?(A B)
    // the sum is confirmed already
    // we need to confirm that this concerns 2x issame (and not 2x sum)
    // we need to confirm that each issame has R and either a literal 1 or 2 (and exactly 2 args)
    TRACE(' - trick_issame_issame_sum');
    TRACE(' - R = sum(A B), S = R ==? 1, T = R ==? 2    =>    S = A !=? B, T = all?(A B)');
    ASSERT(countsR === 3, 'should be 3 links to this sum');
    var issameOffset1 = bounty_getOffset(bounty, indexR, 0);
    var issameOffset2 = bounty_getOffset(bounty, indexR, 1);
    ASSERT(issameOffset1 === sumOffset || issameOffset2 === sumOffset || bounty_getOffset(bounty, indexR, 2) === sumOffset, 'sum should be one of the three');
    if (issameOffset1 === sumOffset) issameOffset1 = bounty_getOffset(bounty, indexR, 2);else if (issameOffset2 === sumOffset) issameOffset2 = bounty_getOffset(bounty, indexR, 2);

    if (ml_dec8(ml, issameOffset1) !== ML_ISSAME || ml_dec8(ml, issameOffset2) !== ML_ISSAME) {
      TRACE(' - this wasnt sum+issame+issame, bailing', ml__opName(ml_dec8(ml, issameOffset1)), ml__opName(ml_dec8(ml, issameOffset2)));
      return false;
    }

    var argCount1 = ml_dec16(ml, issameOffset1 + 1);
    var argCount2 = ml_dec16(ml, issameOffset2 + 1);

    if (argCount1 !== 2 || argCount2 !== 2) {
      TRACE(' - at least one of the issame ops does not have 2 args, bailing');
      return false;
    } // R = sum(A B)      R = sum(A B)
    // S = K ==? L       S = R ==? X
    // T = M ==? N       T = R ==? Y
    //    X==1&Y==2 | X==2&Y==1


    var indexA = readIndex(ml, sumOffset + OFFSET_C_A);
    var indexB = readIndex(ml, sumOffset + OFFSET_C_B);
    var A = getDomain(indexA, true);
    var B = getDomain(indexB, true);
    TRACE(' - A:', domain__debug(A), ', B:', domain__debug(B));

    if (!domain_isBool(A) || !domain_isBool(B)) {
      TRACE(' - A or B wasnt bool, bailing');
      return false;
    }

    var indexK = readIndex(ml, issameOffset1 + OFFSET_C_A);
    var indexL = readIndex(ml, issameOffset1 + OFFSET_C_B);
    var indexS = readIndex(ml, issameOffset1 + OFFSET_C_R);
    var indexM = readIndex(ml, issameOffset2 + OFFSET_C_A);
    var indexN = readIndex(ml, issameOffset2 + OFFSET_C_B);
    var indexT = readIndex(ml, issameOffset2 + OFFSET_C_R);
    ASSERT(indexK === indexR || indexL === indexR, 'R should be arg to this issame');
    var indexX = indexK;
    if (indexX === indexR) indexX = indexL;
    ASSERT(indexM === indexR || indexN === indexR, 'R should be arg to this issame');
    var indexY = indexM;
    if (indexY === indexR) indexY = indexN;
    var X = getDomain(indexX, true);
    var vX = domain_getValue(X);
    var Y = getDomain(indexY, true);
    var vY = domain_getValue(Y);
    TRACE(' - (X)  S=K==?L :', indexS + "=" + indexK + "==?" + indexL, domain__debug(getDomain(indexS, true)), '=', domain__debug(getDomain(indexK, true)), '==?', domain__debug(getDomain(indexL, true)));
    TRACE(' - (Y)  T=M==?N :', indexT + "=" + indexM + "==?" + indexN, domain__debug(getDomain(indexT, true)), '=', domain__debug(getDomain(indexM, true)), '==?', domain__debug(getDomain(indexN, true)));
    TRACE(' - X=', indexX, '=', domain__debug(X), ', Y=', indexY, '=', domain__debug(Y));

    if (vX !== 1 && vX !== 2 || vY !== 1 && vY !== 2 || vX === vY) {
      TRACE(' - issame pattern doesnt match, bailing');
      return false;
    }

    TRACE_MORPH('R = sum(A B), S = R ==? 1, T = R ==? 2', 'S = A !=? B, T = all?(A B)');
    TRACE(' - pattern should match now so we can start the morph. one issame becomes A!=?B, the sum becomes all?(A B), the other issame is eliminated, sum solve stack entry added for R');
    ASSERT(vX === 1 && vY === 2 || vX === 2 && vY === 1, 'we just checked this!');
    solveStack.push(function (_, force, getDomain, setDomain) {
      TRACE(' - trick_issame_issame_sum');
      TRACE(' - ensure the sum result and args are all solved');
      var R = getDomain(indexR); // A and B were confirmed to be bools
      // R is confirmed to be [0 2] (still)

      ASSERT(R === domain_createRange(0, 2)); // Force and sum the values of A and B and set R to that

      var sum = force(indexA) + force(indexB);
      var nR = domain_intersectionValue(R, sum);
      if (R !== nR) setDomain(indexR, nR);
      ASSERT(getDomain(indexA));
      ASSERT(getDomain(indexB));
      ASSERT(getDomain(indexR));
      ASSERT(domain_isSolved(getDomain(indexA)));
      ASSERT(domain_isSolved(getDomain(indexB)));
      ASSERT(domain_isSolved(getDomain(indexR)));
      ASSERT(domain_getValue(getDomain(indexR)) === domain_getValue(getDomain(indexA)) + domain_getValue(getDomain(indexB)));
    }); // T = all?(A B)

    ml_enc8(ml, sumOffset, ML_ISALL);
    ASSERT(argCount === 2, 'change the offset below if this changes');
    ml_enc16(ml, sumOffset + OFFSET_C_C, vX === 2 ? indexS : indexT); // S = A !=? B

    ASSERT(ml_dec16(ml, issameOffset1 + 1) === 2, 'arg count for issame must be 2');
    ml_enc8(ml, issameOffset1, ML_ISDIFF);
    ml_enc16(ml, issameOffset1 + OFFSET_C_A, indexA);
    ml_enc16(ml, issameOffset1 + OFFSET_C_B, indexB);
    ml_enc16(ml, issameOffset1 + OFFSET_C_R, vX === 1 ? indexS : indexT); // Drop the other issame

    ASSERT(ml_dec16(ml, issameOffset2 + 1) === 2, 'arg count for issame must be 2');
    ml_eliminate(ml, issameOffset2, SIZEOF_CR_2);
    bounty_markVar(bounty, indexA);
    bounty_markVar(bounty, indexB);
    bounty_markVar(bounty, indexR);
    bounty_markVar(bounty, indexS);
    bounty_markVar(bounty, indexX);
    bounty_markVar(bounty, indexT);
    bounty_markVar(bounty, indexY);
    somethingChanged();
    return true;
  } // ##############


  function cut_isBoolyOp(opCode, checkMaybes, ml, offset, index) {
    TRACE(' - cut_isBoolyOp, op=', ml__opName(opCode), ', thorough check?', checkMaybes);

    switch (opCode) {
      case ML_LT:
      case ML_LTE:
      case ML_MINUS:
      case ML_DIV:
      case ML_SUM:
      case ML_PRODUCT:
      case ML_DIFF:
      case ML_SAME:
        return ML_BOOLY_NO;

      case ML_XOR:
      case ML_XNOR:
      case ML_IMP:
      case ML_NIMP:
      case ML_ALL:
      case ML_NALL:
      case ML_SOME:
      case ML_NONE:
        return ML_BOOLY_YES;

      case ML_NOLEAF:
        return ML_BOOLY_YES;

      case ML_NOBOOL:
        return ML_BOOLY_NO;

      case ML_ISDIFF:
      case ML_ISSAME:
        // If the var occurs as any of the args, it is not a booly (regardless)
        if (!checkMaybes) return ML_BOOLY_MAYBE;
        TRACE('   - thorough check for', ml__opName(opCode), 'on index=', index);
        var argCount = ml_dec16(ml, offset + 1);

        for (var i = 0; i < argCount; ++i) {
          if (readIndex(ml, offset + SIZEOF_C + i * 2) === index) return ML_BOOLY_NO;
        }

        ASSERT(readIndex(ml, offset + SIZEOF_C + argCount * 2) === index, 'if none of the args is index then R must be index');
        return ML_BOOLY_YES;

      case ML_ISLT:
      case ML_ISLTE:
        // For these ops the result var is fixed in third position
        if (!checkMaybes) return ML_BOOLY_MAYBE;
        TRACE('   - thorough check for', ml__opName(opCode), 'on index=', index);
        if (readIndex(ml, offset + 1) === index || readIndex(ml, offset + 3) === index) return ML_BOOLY_NO;
        ASSERT(readIndex(ml, offset + 5) === index, 'if neither arg then index must be result');
        return ML_BOOLY_YES;

      case ML_ISALL:
      case ML_ISNALL:
      case ML_ISSOME:
      case ML_ISNONE:
        return ML_BOOLY_YES;

      case ML_START:
      case ML_JMP:
      case ML_JMP32:
      case ML_NOOP:
      case ML_NOOP2:
      case ML_NOOP3:
      case ML_NOOP4:
      case ML_STOP:
        return THROW('should not be used for these ops');

      default:
        TRACE('(ml_isBooly) unknown op: ' + opCode);
        THROW('(ml_isBooly) unknown op: ' + opCode);
    }
  }

  function removeOneConstantFromArgs(constantValue, constantArgIndex, argCount, sumOffset) {
    TRACE(' - removeOneConstantFromArgs; only if there is at most one constant at all; const value:', constantValue, ', arg pos:', constantArgIndex, ', args:', argCount, ', op offset:', sumOffset);
    ASSERT(constantArgIndex < argCount, 'arg pos should be valid');

    if (constantArgIndex >= 0) {
      // We want to eliminate the constant arg
      // it may not be in last position (it ought to be but *shrug*), if so simply overwrite it by the last element
      if (constantArgIndex !== argCount - 1) {
        TRACE(' - constant wasnt at end, moving it there now, index=', constantArgIndex, ', argCount=', argCount);
        var lastIndex = readIndex(ml, sumOffset + SIZEOF_C + (argCount - 1) * 2);
        ml_enc16(ml, sumOffset + SIZEOF_C + constantArgIndex * 2, lastIndex); // We want to drop the constant so we dont need to copy that back
      }

      TRACE(' - constant is (now) at the end, reducing arg count to drop it from', argCount, 'to', argCount - 1);
      TRACE(' - op before:', ml__debug(ml, sumOffset, 1, problem));
      ASSERT(domain_getValue(getDomain(readIndex(ml, sumOffset + SIZEOF_C + (argCount - 1) * 2), true)) === constantValue, 'the constant should now be in last position of the sum'); // Reduce sum arg count

      --argCount;
      ml_enc16(ml, sumOffset + 1, argCount); // Note: no need to copy R one position back because we will explicitly write an S there anyways
      // write a jump in the new open space

      ml_enc8(ml, sumOffset + SIZEOF_C + (argCount + 1) * 2, ML_NOOP2);
      TRACE(' - op after:', ml__debug(ml, sumOffset, 1, problem));
      ASSERT(ml_validateSkeleton(ml, 'removeOneConstantFromArgs; after constant elimination'));
    }

    return argCount;
  }

  function addSumToSolveStack(indexR, args, constantValue) {
    TRACE(' - adding solvestack entry for isnone/isall/issome/isnall');
    TRACE(' - args sum to', domain__debug(args.map(getDomain).reduce(function (a, b) {
      return domain_plus(a, b);
    })), ', constant:', constantValue, ', total:', domain__debug(domain_plus(domain_createValue(constantValue), args.map(getDomain).reduce(function (a, b) {
      return domain_plus(a, b);
    }))), ', R=', domain__debug(getDomain(indexR)), ', all args:', args.map(getDomain).map(domain__debug).join(' '));
    ASSERT(domain_intersection(getDomain(indexR), domain_plus(domain_createValue(constantValue), args.map(getDomain).reduce(function (a, b) {
      return domain_plus(a, b);
    }))) === getDomain(indexR), 'R should be able to reflect the outcome of summing any of its args'); // Note: either way, R must reflect the sum of its args. so its the same solve

    solveStack.push(function (_, force, getDomain, setDomain) {
      TRACE(' - addSumToSolveStack; cut sum+reifier -> isnone/issome/isall/isnall');
      var oR = getDomain(indexR);
      var vR = 0;

      for (var i = 0, n = args.length; i < n; ++i) {
        var vN = force(args[i]);
        ASSERT((vN & 1) >= 0, 'should be bool');
        if (vN) ++vR;
      }

      var R = domain_intersectionValue(oR, vR + constantValue);
      ASSERT(R, 'R should be able to reflect the solution');
      if (oR !== R) setDomain(indexR, R);
    });
  }

  function cutAddPseudoBoolyAlias(indexKeep, indexEliminate) {
    var oE = getDomain(indexEliminate, true); // Remember what E was because it will be replaced by false to mark it an alias

    TRACE(' - pseudo-alias for booly xnor arg;', indexKeep, '@', indexEliminate, '  ->  ', domain__debug(getDomain(indexKeep)), '@', domain__debug(getDomain(indexEliminate)), 'replacing', indexEliminate, 'with', indexKeep);
    var XNOR_EXCEPTION = true;
    solveStack.push(function (_, force, getDomain, setDomain) {
      TRACE(' - cutAddPseudoBoolyAlias');
      TRACE(' -', indexKeep, '!^', indexEliminate, '  ->  ', domain__debug(getDomain(indexKeep)), '!^', domain__debug(oE));
      var vK = force(indexKeep);
      var E;

      if (vK === 0) {
        E = domain_removeGtUnsafe(oE, 0);
      } else {
        E = domain_removeValue(oE, 0);
      }

      TRACE('  -> updating', domain__debug(oE), 'to', domain__debug(E));
      ASSERT(E, 'E should be able to reflect the solution'); // Always set it even if oE==E

      setDomain(indexEliminate, E, true, XNOR_EXCEPTION);
    }); // Note: addAlias will push a defer as well. since the defers are resolved in reverse order,
    // we must call addAlias after adding our own defer, otherwise our change will be lost.

    addAlias(indexEliminate, indexKeep, 'cutAddPseudoBoolyAlias');
  }

  function markAndCollectArgs(ml, opOffset, argCount, except) {
    if (except === void 0) {
      except = -1;
    }

    TRACE(' - markAndCollectArgs, from offset', opOffset, 'for', argCount, 'vars');
    var args = [];

    for (var i = 0; i < argCount; ++i) {
      var index = readIndex(ml, opOffset + SIZEOF_C + i * 2);
      if (index !== except) args.push(index);
      bounty_markVar(bounty, index);
    }

    return args;
  }

  function markAllArgs(ml, opOffset, argCount) {
    for (var i = 0; i < argCount; ++i) {
      var index = readIndex(ml, opOffset + SIZEOF_C + i * 2);
      bounty_markVar(bounty, index);
    }
  }

  function cut_moveTo(ml, offset, len) {
    TRACE(' - trying to move from', offset, 'to', offset + len, 'delta = ', len);

    switch (ml_dec8(ml, offset + len)) {
      case ML_NOOP:
      case ML_NOOP2:
      case ML_NOOP3:
      case ML_NOOP4:
      case ML_JMP:
      case ML_JMP32:
        TRACE('  - moving to another jump so merging them now');
        ml_compileJumpAndConsolidate(ml, offset, len);
        pc = offset; // Restart, make sure the merge worked

        break;

      default:
        pc = offset + len;
        break;
    }
  }
}

var __runCounter = 0;
var __opCounter = 0;

function deduper(ml, problem) {
  ++__runCounter;
  TRACE('\n ## pr_dedupe, counter=', __runCounter, ',ml=', ml.length < 50 ? ml.join(' ') : '<big>');
  var getDomain = problem.getDomain,
      setDomain = problem.setDomain,
      getAlias = problem.getAlias,
      addVar = problem.addVar,
      addAlias = problem.addAlias;
  var pc = 0;
  var constraintHash = {}; // Keys are A@B or R=A@B and the vars can be an index (as is) or a literal prefixed with #

  var debugHash = {};
  var removed = 0;
  var aliased = 0;
  var emptyDomain = false;
  innerLoop();
  getTerm().log(' - dedupe removed', removed, 'constraints and aliased', aliased, 'result vars, emptyDomain=', emptyDomain, ', processed', __opCounter, 'ops');
  TRACE(m2d__debug(problem));
  return emptyDomain ? -1 : aliased; // If aliases were created the minifier will want another go.

  function dedupePairOc2(op) {
    var indexA = getAlias(ml_dec16(ml, pc + OFFSET_C_A));
    var indexB = getAlias(ml_dec16(ml, pc + OFFSET_C_B));
    var key = op + ':' + indexA + ',' + indexB;
    var debugString = op + ':' + domain__debug(getDomain(indexA, true)) + ',' + domain__debug(getDomain(indexB, true));

    if (op === '<' || op === '<=') {
      if (checkLtLteFromRegular(op, indexA, indexB, debugString)) return;
    } // Below this line no more deduping, only appending


    if (constraintHash[key] !== undefined) {
      TRACE(' - dedupePairOc2; Found dupe constraint; eliminating the second one');
      TRACE('    - #1:', debugHash[key]);
      TRACE('    - #2:', debugString);
      ml_eliminate(ml, pc, SIZEOF_C_2);
      return;
    }

    constraintHash[key] = 1;
    debugHash[key] = debugString;
    pc += SIZEOF_C_2;
  }

  function checkLtLteFromRegular(op, indexA, indexB, debugString) {
    // Check whether reifiers have matching non-reifiers (valid artifacts), so `R=A<?B` and `A<B` means `R>0`
    // R>0 when: '<? <' '<=? <' '<=? <='
    // R=? when: '<? <=' (because the A==B case always passes '<=' while '<?' depends on R)
    TRACE('   - checking for matching regular inverted constraints');
    ASSERT(op === '<' || op === '<=', 'update this code if this assertion changes', op); // Search for
    // - R=A<?B A<B
    // - R=A<=?B A<B
    // - R=A<=?B A<=B
    // => R>0

    if (op === '<' && checkLtLteFromRegularAB('<?', '<', indexA, indexB, debugString)) return true;
    if (op === '<' && checkLtLteFromRegularAB('<=?', '<', indexA, indexB, debugString)) return true;
    if (op === '<=' && checkLtLteFromRegularAB('<=?', '<=', indexA, indexB, debugString)) return true; // Search for
    // - R=A<?B B<A
    // - R=A<?B B<=A
    // - R=A<=?B B<A
    // => R=0

    if (op === '<' && checkLtLteFromRegularBA('<?', '<', indexA, indexB, debugString)) return true;
    if (op === '<=' && checkLtLteFromRegularBA('<?', '<=', indexA, indexB, debugString)) return true;
    if (op === '<' && checkLtLteFromRegularBA('<=?', '<', indexA, indexB, debugString)) return true;
    return false;
  }

  function checkLtLteFromRegularAB(rifop, regop, indexA, indexB, debugString) {
    var rifKey = rifop + ':R=' + indexA + ',' + indexB;
    var reifierOffset = constraintHash[rifKey];

    if (reifierOffset) {
      var indexR = getAlias(ml_dec16(ml, reifierOffset + 5));
      var R = getDomain(indexR, true);
      if (!domain_isBooly(R)) return false;
      TRACE(' - checkLtLteFromReifierAB; found `R=A' + rifop + 'B` and `A' + regop + 'B`, eliminating reifier and booly-solving R, R=', domain__debug(R));
      TRACE('    - #1:', debugHash[rifKey]);
      TRACE('    - #2:', debugString);
      ml_eliminate(ml, reifierOffset, SIZEOF_VVV);
      TRACE(' - Removing 0 from R');
      setDomain(indexR, domain_removeValue(R, 0));
      return true;
    }

    return false;
  }

  function checkLtLteFromRegularBA(rifop, regop, indexA, indexB, debugString) {
    var invRifKey = rifop + ':R=' + indexB + ',' + indexA;
    var reifierOffset = constraintHash[invRifKey];

    if (reifierOffset) {
      var indexR = getAlias(ml_dec16(ml, reifierOffset + 5));
      var R = getDomain(indexR, true);
      if (!domain_isBooly(R)) return false;
      TRACE(' - checkLtLteFromReifierBA; found `R=A' + rifop + 'B` and `B' + regop + 'A`, eliminating reifier and booly-solving R, R=', domain__debug(R));
      TRACE('    - #1:', debugHash[invRifKey]);
      TRACE('    - #2:', debugString);
      ml_eliminate(ml, reifierOffset, SIZEOF_VVV);
      TRACE(' - Setting R to 0');
      setDomain(indexR, domain_removeGtUnsafe(R, 0));
      return true;
    }

    return false;
  }

  function dedupeTripO(op) {
    // This assumes the assignment is a fixed value, not booly like reifiers
    // because in this case we can safely alias any R that with the same A@B
    var indexA = getAlias(ml_dec16(ml, pc + 1));
    var indexB = getAlias(ml_dec16(ml, pc + 3));
    var indexR = getAlias(ml_dec16(ml, pc + 5));
    var key = op + ':' + indexA + ',' + indexB;
    var debugString = op + ':' + domain__debug(getDomain(indexR, true)) + '=' + domain__debug(getDomain(indexA, true)) + ',' + domain__debug(getDomain(indexB, true));
    var index = constraintHash[key];

    if (index !== undefined) {
      index = getAlias(index);
      TRACE(' - dedupeTripO; Found dupe constraint; eliminating the second one, aliasing', indexR, 'to', index);
      TRACE('    - #1:', debugHash[key]);
      TRACE('    - #2:', debugString);
      ml_eliminate(ml, pc, SIZEOF_VVV);

      if (indexR !== index) {
        var R = domain_intersection(getDomain(indexR, true), getDomain(index, true));
        if (!R) return emptyDomain = true; // This probably wont matter for most of the cases, but it could make a difference
        // setDomain(indexR, R); // (useless)

        setDomain(index, R);
        addAlias(indexR, index);
      }

      return;
    }

    constraintHash[key] = indexR;
    debugHash[key] = debugString;
    pc += SIZEOF_VVV;
  }

  function dedupeIsltIslte(op) {
    // Islt, islte
    var offset = pc;
    var indexA = getAlias(ml_dec16(ml, pc + 1));
    var indexB = getAlias(ml_dec16(ml, pc + 3));
    var indexR = getAlias(ml_dec16(ml, pc + 5)); // We'll add a key by all three indexes and conditionally also on the args and the domain of R

    var key = op + ':' + indexR + '=' + indexA + ',' + indexB;
    var debugString = op + ':' + domain__debug(getDomain(indexR, true)) + '=' + domain__debug(getDomain(indexA, true)) + ',' + domain__debug(getDomain(indexB, true));
    TRACE('   - key=', key, ';', constraintHash[key] !== undefined);

    if (constraintHash[key] !== undefined) {
      TRACE(' - dedupeReifierTripU; Found dupe constraint; eliminating the second one');
      TRACE('    - #1:', debugHash[key]);
      TRACE('    - #2:', debugString);
      ml_eliminate(ml, pc, SIZEOF_VVV);
      return;
    }

    var R = getDomain(indexR, true);
    TRACE('   - checking for matching regular constraints');
    ASSERT(op.slice(0, -1) === '<' || op.slice(0, -1) === '<=', 'update this code if this assertion changes');
    var regkey = op.slice(0, -1) + ':' + indexA + ',' + indexB;

    if (constraintHash[regkey]) {
      TRACE(' - dedupeReifierTripU; found R=A' + op + 'B and A' + op.slice(0, -1) + 'B, eliminating reifier and forcing R to truthy if R has a nonzero, R=', domain__debug(R));

      if (!domain_isZero(R)) {
        // Has non-zero
        TRACE('    - #1:', debugHash[regkey]);
        TRACE('    - #2:', debugString);
        ml_eliminate(ml, pc, SIZEOF_VVV);
        TRACE(' - Removing 0 from R');
        setDomain(indexR, domain_removeValue(R, 0));
        return;
      }
    }

    if (checkLtLteFromReifier(op, indexA, indexB, indexR, R, debugString)) return;
    var invkey = (op === '<?' ? '<=?' : '<?') + ':R=' + indexB + ',' + indexA;
    var invOffset = constraintHash[invkey];

    if (invOffset) {
      // One of:
      // R = A <? B, S = B <=? A
      // R = A <=? B, S = B <? A
      // (note: not <?<? nor <=?<=? because they are NOT their own inverse)
      TRACE(' - Found `', op === '<?' ? 'R = A <? B, S = B <=? A' : 'R = A <=? B, S = B <? A', '`');
      var indexS = getAlias(ml_dec16(ml, invOffset + 5));
      TRACE(' - morphing one op to `R ^ S`;', domain__debug(getDomain(indexR)), '^', domain__debug(getDomain(indexS)));
      ml_vvv2c2(ml, offset, ML_XOR, indexR, indexS);
      return;
    }

    TRACE('   - R:', domain__debug(R), ', size=', domain_size(R), ', has zero:', !domain_hasNoZero(R), '--> is safe?', domain_isBoolyPair(R));

    if (domain_isBoolyPair(R)) {
      // Okay R has only two values and one of them is zero
      // try to match the arg constraints only. if we find a dupe with
      // the same R domain then we can alias that R with this one
      // otherwise the two R's are pseudo xnor aliases
      // we'll encode the domain instead of indexR to prevent
      // multiple args on different R's to clash
      // while R may not look it, it still represents a unique domain so we can use the
      // encoded value as is here. wrap it to prevent clashes with indexes and numdoms
      var key2 = op + ':[' + R + ']' + '=' + indexA + ',' + indexB;
      TRACE('   - key2:', key2);
      var index = constraintHash[key2];

      if (index !== undefined) {
        index = getAlias(index);
        TRACE(' - dedupeIsltIslte; Found dupe reifier; eliminating the second one, aliasing', indexR, 'to', index);
        TRACE('    - #1:', debugHash[key2]);
        TRACE('    - #2:', debugString);
        ml_eliminate(ml, pc, SIZEOF_VVV);

        if (indexR === index) {
          TRACE(' - same indexes (perhaps aliased) so dont alias them here');
        } else {
          addAlias(indexR, index);
        }

        return;
      }

      constraintHash[key2] = indexR;
      debugHash[key2] = debugString;
    }

    constraintHash[key] = 1;
    debugHash[key] = debugString;
    var keyr = op + ':R=' + indexA + ',' + indexB;
    constraintHash[keyr] = offset;
    debugHash[keyr] = debugString;
    pc += SIZEOF_VVV;
  }

  function checkLtLteFromReifier(op, indexA, indexB, indexR, R, debugString) {
    // Check whether reifiers have matching non-reifiers (valid artifacts), so `R=A<?B` and `A<B` means `R>0`
    // R>0 when: '<? <' '<=? <' '<=? <='
    // R=? when: '<? <=' (because the A==B case always passes '<=' while '<?' depends on R)
    TRACE('   - checking for matching regular inverted constraints');
    var regop = op.slice(0, -1);
    ASSERT(regop === '<' || regop === '<=', 'update this code if this assertion changes');

    if (domain_isBooly(R)) {
      // Search for
      // - R=A<?B A<B
      // - R=A<=?B A<B
      // - R=A<=?B A<=B
      // => R>0
      if (op === '<?' && checkLtLteFromReifierAB('<?', '<', indexA, indexB, indexR, R, debugString)) return true;
      if (op === '<=?' && checkLtLteFromReifierAB('<=?', '<', indexA, indexB, indexR, R, debugString)) return true;
      if (op === '<=?' && checkLtLteFromReifierAB('<=?', '<=', indexA, indexB, indexR, R, debugString)) return true; // Search for
      // - R=A<?B B<A
      // - R=A<?B B<=A
      // - R=A<=?B B<A
      // => R=0

      if (op === '<?' && checkLtLteFromReifierBA('<?', '<', indexA, indexB, indexR, R, debugString)) return true;
      if (op === '<?' && checkLtLteFromReifierBA('<?', '<=', indexA, indexB, indexR, R, debugString)) return true;
      if (op === '<=?' && checkLtLteFromReifierBA('<=?', '<', indexA, indexB, indexR, R, debugString)) return true;
    }

    return false;
  }

  function checkLtLteFromReifierAB(rifop, regop, indexA, indexB, indexR, R, debugString) {
    var regkey = regop + ':' + indexA + ',' + indexB;

    if (constraintHash[regkey]) {
      TRACE(' - checkLtLteFromReifierAB; found `R=A' + rifop + 'B` and `A' + regop + 'B`, eliminating reifier and booly-solving R, R=', domain__debug(R));
      TRACE('    - #1:', debugHash[regkey]);
      TRACE('    - #2:', debugString);
      ml_eliminate(ml, pc, SIZEOF_VVV);
      TRACE(' - Removing 0 from R');
      setDomain(indexR, domain_removeValue(R, 0));
      return true;
    }

    return false;
  }

  function checkLtLteFromReifierBA(rifop, regop, indexA, indexB, indexR, R, debugString) {
    var reginvkey = regop + ':' + indexB + ',' + indexA;

    if (constraintHash[reginvkey]) {
      TRACE(' - checkLtLteFromReifierBA; found `R=A' + rifop + 'B` and `B' + regop + 'A`, eliminating reifier and booly-solving R, R=', domain__debug(R));
      TRACE('    - #1:', debugHash[reginvkey]);
      TRACE('    - #2:', debugString);
      ml_eliminate(ml, pc, SIZEOF_VVV);
      TRACE(' - Setting R to 0');
      setDomain(indexR, domain_removeGtUnsafe(R, 0));
      return true;
    }

    return false;
  }

  function dedupeBoolyList(op) {
    // Isall, isnall, isnone, issome
    // the tricky example:
    // ####
    // : A, B, C 1
    // : R [0 1]
    // : S [0 0 2 2]
    // R = xxx?(A B C)
    // S = xxx?(A B C)
    // ####
    // in this case R and S are "booly alias" but not actual alias
    // basically this translates into a xnor (if R then S, if S then R)
    var argCount = ml_dec16(ml, pc + 1);
    var opSize = SIZEOF_C + argCount * 2 + 2;
    TRACE(' - dedupeBoolyList; args:', argCount, ', opsize:', opSize); // First we want to sort the list. we'll do this inline to prevent array creation

    ml_heapSort16bitInline(ml, pc + SIZEOF_C, argCount); // Now collect them. the key should end up with an ordered list

    var args = '';
    var debugArgs = '';

    for (var i = 0; i < argCount; ++i) {
      var index = getAlias(ml_dec16(ml, pc + SIZEOF_C + i * 2));
      args += index + ' ';
      debugArgs += domain__debug(getDomain(index, true));
    }

    var indexR = getAlias(ml_dec16(ml, pc + SIZEOF_C + argCount * 2)); // We'll add a key with indexR and conditionally one with just the domain of R

    var key = op + ':' + indexR + '=' + args;
    var debugString = op + ':' + domain__debug(getDomain(indexR, true)) + '=' + debugArgs;
    TRACE('   - key=', key, ';', constraintHash[key] !== undefined);

    if (constraintHash[key] !== undefined) {
      TRACE(' - dedupeBoolyList; Found dupe constraint; eliminating the second one');
      TRACE('    - #1:', debugHash[key]);
      TRACE('    - #2:', debugString);
      ml_eliminate(ml, pc, opSize);
      return;
    }

    constraintHash[key] = 1;
    debugHash[key] = debugString;
    var R = getDomain(indexR, true);
    TRACE('   - R:', domain__debug(R), '--> is safe?', domain_isBoolyPair(R));

    if (domain_isBoolyPair(R)) {
      // Okay R has only two values and one of them is zero
      // try to match the arg constraints only. if we find a dupe with
      // the same R domain then we can alias that R with this one
      // we'll encode the domain instead of indexR to prevent
      // multiple args on different R's to clash
      // while R may not look it, it still represents a unique domain so we can use the
      // encoded value as is here. wrap it to prevent clashes with indexes and numdoms
      var key2 = op + ':[' + R + ']' + '=' + args;
      TRACE('   - key2:', key2);
      var _index = constraintHash[key2];

      if (_index !== undefined) {
        _index = getAlias(_index);
        TRACE(' - dedupeBoolyList; Found dupe reifier; eliminating the second one, aliasing', indexR, 'to', _index);
        TRACE('    - #1:', debugHash[key2]);
        TRACE('    - #2:', debugString);
        ml_eliminate(ml, pc, opSize);

        if (indexR === _index) {
          TRACE(' - same indexes (perhaps aliased) so dont alias them here');
        } else {
          ASSERT(getDomain(indexR) === getDomain(_index), 'should have already asserted that these two domains have only two values, a zero and a non-zero, and that they are equal');
          addAlias(indexR, _index);
        }

        return;
      }

      constraintHash[key2] = indexR;
      debugHash[key2] = debugString;
    }

    TRACE(' - (no action, dedupeBoolyList)');
    pc += opSize;
  }

  function dedupeNonBoolyList(op) {
    // Sum, product
    var argCount = ml_dec16(ml, pc + 1);
    var opSize = SIZEOF_C + argCount * 2 + 2; // First we want to sort the list. we'll do this inline to prevent array creation

    ml_heapSort16bitInline(ml, pc + SIZEOF_C, argCount); // Now collect them. the key should end up with an ordered list

    var args = '';
    var debugArgs = '';

    for (var i = 0; i < argCount; ++i) {
      var argIndex = getAlias(ml_dec16(ml, pc + SIZEOF_C + i * 2));
      args += argIndex + ' ';
      debugArgs += domain__debug(getDomain(argIndex, true));
    }

    var indexR = getAlias(ml_dec16(ml, pc + SIZEOF_C + argCount * 2)); // We'll add a key without indexR because the results of these ops are fixed (unlike booly ops)

    var key = op + ':' + '=' + args;
    var debugString = op + ':' + debugArgs;
    var index = constraintHash[key];

    if (index !== undefined) {
      index = getAlias(index);
      TRACE(' - dedupeNonBoolyList; Found dupe reifier; eliminating the second one, aliasing', indexR, 'to', index);
      TRACE('    - #1:', debugHash[key]);
      TRACE('    - #2:', debugString);
      ml_eliminate(ml, pc, opSize);

      if (indexR !== index) {
        // R = A <=? A (artifact)
        var domain = domain_intersection(getDomain(index, true), getDomain(indexR, true));
        setDomain(index, domain);
        addAlias(indexR, index);
      }

      return;
    }

    constraintHash[key] = indexR;
    debugHash[key] = debugString;
    pc += opSize;
  }

  function dedupeVoidList(op) {
    // Sum, product
    var argCount = ml_dec16(ml, pc + 1);
    var opSize = SIZEOF_C + argCount * 2; // First we want to sort the list. we'll do this inline to prevent array creation

    ml_heapSort16bitInline(ml, pc + SIZEOF_C, argCount); // Now collect them. the key should end up with an ordered list

    var args = '';
    var debugArgs = '';

    for (var i = 0; i < argCount; ++i) {
      var argIndex = getAlias(ml_dec16(ml, pc + SIZEOF_C + i * 2));
      args += argIndex + ' ';
      debugArgs += domain__debug(getDomain(argIndex, true));
    }

    var key = op + ':' + '=' + args;
    var debugString = op + ':' + debugArgs;

    if (constraintHash[key] !== undefined) {
      TRACE(' - dedupeVoidList; Found dupe constraint; eliminating the second one');
      TRACE('    - #1:', debugHash[key]);
      TRACE('    - #2:', debugString);
      ml_eliminate(ml, pc, opSize);
      return;
    }

    constraintHash[key] = 1;
    debugHash[key] = debugString;
    pc += opSize;
  }

  function dedupeInvIsSameIsDiff(op) {
    TRACE(' - dedupeInvIsSameIsDiff;', op); // Looking for this pattern:
    // : X [2 3]
    // R = X ==? 2
    // S = X !=? 3
    // which means R !^ S, or even == when R and S are size=2,min=0,R==S

    var argCount = ml_dec16(ml, pc + 1);

    if (argCount !== 2) {
      // TODO: support any number of args here
      TRACE('   - arg count != 2 so bailing, for now');
      return false;
    }

    var indexA = getAlias(ml_dec16(ml, pc + OFFSET_C_A));
    var indexB = getAlias(ml_dec16(ml, pc + OFFSET_C_B));
    var indexR = getAlias(ml_dec16(ml, pc + OFFSET_C_R)); // If A or B is a constant, then B will be a constant afterwards, and A (only) as well if they are both constants

    if (indexB < indexA) {
      var t = indexB;
      indexB = indexA;
      indexA = t;
    }

    var A = getDomain(indexA, true);
    var B = getDomain(indexB, true); // Verify fingerprint

    if (domain_size(A) !== 2) {
      TRACE(' - size(A) != 2, bailing');
      return false;
    }

    var vB = domain_getValue(B);

    if (vB < 0 || !domain_containsValue(A, vB)) {
      TRACE(' - B wasnt a constant or A didnt contain B, bailing', domain__debug(A), domain__debug(B));
      return false;
    } // Fingerprint matches. A contains the solved value B and one other value
    // check if opposite op is known


    var invA = domain_removeValue(A, vB);
    ASSERT(domain_isSolved(invA), 'if A had two values and one of them vB, then invA should have one value');
    var otherValue = domain_getValue(invA);
    var indexInvA = addVar(undefined, otherValue, false, false, true); // Just gets the index for this constant

    ASSERT(getDomain(indexInvA) === domain_createValue(otherValue), 'should alias to a constant');
    var invOp = op === 'issame' ? 'isdiff' : 'issame';
    var key = invOp + ':' + indexA + ',' + indexInvA;
    var debugString = op + ':' + domain__debug(getDomain(indexR, true)) + '=' + domain__debug(getDomain(indexA, true)) + ',' + domain__debug(getDomain(indexB, true));
    var indexS = constraintHash[key];

    if (indexS === undefined) {
      var thisKey = op + ':' + indexA + ',' + indexB;
      TRACE(' - opposite for ' + op + ' (' + invOp + ') doesnt exist, adding this key then bailing');
      TRACE(' - checked for key=', key, ', now adding key:', thisKey);
      constraintHash[thisKey] = indexR;
      debugHash[thisKey] = debugString;
      return false;
    }

    TRACE(' - found the opposite of this constraint;');
    TRACE('    - #1:', debugHash[key]);
    TRACE('    - #2:', debugString);
    TRACE(' - indexR !^ indexS, and perhaps indexR == indexS, check that case first');
    ASSERT(argCount === 2, 'should have two args');
    var R = getDomain(indexR, true);

    if (domain_size(R) === 2 && !domain_hasNoZero(R) && R === getDomain(indexS, true)) {
      TRACE(' - indexR == indexS because', domain__debug(R), 'has two elements, one of them zero, and R==S');

      if (indexR === indexS) {
        TRACE(' - var is same so skipping alias');
      } else {
        addAlias(indexR, indexS);
      }

      ml_eliminate(ml, pc, SIZEOF_CR_2);
    } else {
      TRACE(' - indexR !^ indexS because R=', domain__debug(R), ', S=', domain__debug(getDomain(indexS, true)), '; R may still end up with a different value from S');
      TRACE(' - morphing to an xnor(R S);', ml_getOpSizeSlow(ml, pc), SIZEOF_C + 2 * 2 + 2);
      ASSERT(ml_getOpSizeSlow(ml, pc) >= SIZEOF_C + 2 * 2 + 2, 'the current op should have at least the required space for a 2 arg xnor', ml_getOpSizeSlow(ml, pc));
      ml_cr2c2(ml, pc, argCount, ML_XNOR, indexR, indexS);
    } // Dont update pc


    return true;
  }

  function innerLoop() {
    while (pc < ml.length && !emptyDomain) {
      ++__opCounter;
      var op = ml[pc];
      TRACE(' -- DD pc=' + pc + ', op: ' + ml__debug(ml, pc, 1, problem, true));

      switch (op) {
        case ML_IMP:
          dedupePairOc2('->');
          break;

        case ML_NIMP:
          dedupePairOc2('!->');
          break;

        case ML_ISLT:
          dedupeIsltIslte('<?');
          break;

        case ML_ISLTE:
          dedupeIsltIslte('<=?');
          break;

        case ML_ISALL:
          dedupeBoolyList('isall');
          break;

        case ML_ISDIFF:
          if (!dedupeInvIsSameIsDiff('isdiff')) dedupeBoolyList('isdiff');
          break;

        case ML_ISNALL:
          dedupeBoolyList('isnall');
          break;

        case ML_ISNONE:
          dedupeBoolyList('isnone');
          break;

        case ML_ISSAME:
          if (!dedupeInvIsSameIsDiff('issame')) dedupeBoolyList('issame');
          break;

        case ML_ISSOME:
          dedupeBoolyList('issome');
          break;

        case ML_ALL:
          dedupeVoidList('all');
          break;

        case ML_DIFF:
          dedupeVoidList('diff');
          break;

        case ML_LT:
          dedupePairOc2('<');
          break;

        case ML_LTE:
          dedupePairOc2('<=');
          break;

        case ML_NALL:
          dedupeVoidList('nall');
          break;

        case ML_NONE:
          dedupeVoidList('none');
          break;

        case ML_SAME:
          dedupeVoidList('same');
          break;

        case ML_SOME:
          dedupeVoidList('some');
          break;

        case ML_XNOR:
          dedupeVoidList('xnor');
          break;

        case ML_XOR:
          dedupeVoidList('^');
          break;

        case ML_MINUS:
          dedupeTripO('-');
          break;

        case ML_DIV:
          dedupeTripO('/');
          break;

        case ML_SUM:
          dedupeNonBoolyList('sum');
          break;

        case ML_PRODUCT:
          dedupeNonBoolyList('product');
          break;

        case ML_START:
          if (pc !== 0) {
            return ml_throw(ml, pc, 'deduper problem found START');
          }

          ++pc;
          break;

        case ML_STOP:
          return constraintHash;

        case ML_NOBOOL: // No deduping this!

        case ML_NOLEAF:
          // No deduping this!
          pc += SIZEOF_V;
          break;

        case ML_JMP:
          pc += SIZEOF_V + ml_dec16(ml, pc + 1);
          break;

        case ML_JMP32:
          pc += SIZEOF_W + ml_dec32(ml, pc + 1);
          break;

        case ML_NOOP:
          ++pc;
          break;

        case ML_NOOP2:
          pc += 2;
          break;

        case ML_NOOP3:
          pc += 3;
          break;

        case ML_NOOP4:
          pc += 4;
          break;

        default:
          ml_throw(ml, pc, '(dd) unknown op');
      }
    }

    if (!emptyDomain) ml_throw(ml, pc, '(dd) ML OOB');
  }
}

// This is an import function for config

var $$AND = 38;
var $$AT = 64;
var $$BANG = 33;
var $$COLON = 58;
var $$COMMA = 44;
var $$CR = 10;
var $$LF = 13;
var $$DASH = 45;
var $$DIV = 47;
var $$EQ = 61;
var $$GT = 62;
var $$HASH = 35;
var $$LEFTBRACK = 91;
var $$LEFTPAREN = 40;
var $$LT = 60;
var $$OR = 124;
var $$PLUS = 43;
var $$QM = 63;
var $$SPACE = 32;
var $$RIGHTBRACK = 93;
var $$RIGHTPAREN = 41;
var $$SQUOTE = 39;
var $$STAR = 42;
var $$TAB = 9;
var $$XOR = 94;
var $$0 = 48;
var $$1 = 49;
var $$2 = 50;
var $$3 = 51;
var $$4 = 52;
var $$5 = 53;
var $$6 = 54;
var $$7 = 55;
var $$8 = 56;
var $$9 = 57;
var $$a = 97;
var $$c = 99;
var $$d = 100;
var $$e = 101;
var $$f = 102;
var $$g = 103;
var $$i = 105;
var $$l = 108;
var $$m = 109;
var $$n = 110;
var $$o = 111;
var $$p = 112;
var $$r = 114;
var $$s = 115;
var $$t = 116;
var $$x = 120;
var $$z = 122;
var $$A = 65;
var $$Z = 98;
/**
 * Compile the constraint dsl to a bytecode
 *
 * @param {string} dslStr
 * @param {Object} problem
 * @param {boolean} [_debug] Improved error reporting when true
 * @returns {string}
 */

function dsl2ml(dslStr, problem, _debug) {
  TRACE('# dsl2ml:', [dslStr.slice(0, 100).replace(/ +/g, ' ') + (dslStr.replace(/ +/g, ' ').length > 100 ? '...' : '')]);
  problem.input.varstrat = 'default';
  problem.input.valstrat = 'default';
  problem.input.dsl = dslStr;
  var addVar = problem.addVar,
      setDomain = problem.setDomain,
      name2index = problem.name2index;
  var constraints = 0;
  var freeDirective = -1; // For `@custom free x`. this var tries to ensure exactly x bytes are "free"

  var dslPointer = 0;
  var dslBuf;

  if (typeof Buffer === 'undefined') {
    dslBuf = new window.TextEncoder('utf-8').encode(dslStr);
  } else {
    dslBuf = new Uint8Array(Buffer.from(dslStr, 'binary'));
  }

  ASSERT(dslBuf instanceof Uint8Array);
  var len = dslBuf.length;
  var mlBufSize = Math.ceil(dslBuf.length / 5); // 20% is arbitrary choice. grown dynamically when needed

  var mlBuffer = new Uint8Array(mlBufSize).fill(0);
  var mlPointer = 0; // This is for a hack

  var lastAssignmentIndex = -1;
  var lastUnknownIndex = -1;
  encode8bit(ML_START);

  while (!isEof()) {
    parseStatement();
  }

  if (freeDirective > 0) {
    // Compile a jump of given size. this will be considered available space
    TRACE('forcing', freeDirective, 'bytes of available space');
    compileJump(freeDirective);
  }

  encode8bit(ML_STOP); // This step will be undone but serves to ensure the buffer isnt grown in the actual compilation step (which happens after the available-space-checks)

  --mlPointer;

  if (freeDirective < 0) {
    // Compile a jump for the remainder of the space, if any, which could be used by the recycle mechanisms
    // only do this here when the free directive is absent
    var leftFree = mlBufSize - mlPointer - 1; // STOP will occupy 1 byte

    TRACE('space available', leftFree, 'bytes');
    if (leftFree > 0) compileJump(leftFree);
  }

  encode8bit(ML_STOP); // Put the STOP at the end
  // if there is now still space left, we need to crop it because freeDirective was set and didnt consume it all

  if (mlBufSize - mlPointer) {
    TRACE('cropping excess available space', mlBufSize, mlPointer, mlBufSize - mlPointer); // If the free directive was given, remove any excess free space
    // note that one more byte needs to be compiled after this (ML_STOP)

    mlBuffer.splice(mlPointer);
  }

  ASSERT(mlPointer === mlBuffer.length, 'mlPointer should now be at the first unavailable cell of the buffer', mlPointer, mlBuffer.length, mlBuffer);
  problem.ml = mlBuffer;
  if (!problem.input.targets) problem.input.targets = 'all';
  getTerm().log('# dsl2ml: parsed', constraints, 'constraints and', problem.domains.length, 'vars'); // ########################################################################

  function startConstraint(op) {
    ++constraints;
    encode8bit(op);
  }

  function encode8bit(num) {
    ASSERT(typeof num === 'number' && num >= 0 && num <= 0xff, 'OOB number');
    TRACE('encode8bit:', num, 'dsl pointer:', dslPointer, ', ml pointer:', mlPointer);
    if (mlPointer >= mlBufSize) grow();
    mlBuffer[mlPointer++] = num;
  }

  function encode16bit(num) {
    TRACE('encode16bit:', num, '->', num >> 8, num & 0xff, 'dsl pointer:', dslPointer, ', ml pointer:', mlPointer, '/', mlBufSize);
    ASSERT(typeof num === 'number', 'Encoding 16bit must be num', typeof num, num);
    ASSERT(num >= 0, 'OOB num', num);
    if (num > 0xffff) THROW('Need 32bit num support but missing it');
    if (mlPointer >= mlBufSize - 1) grow();
    mlBuffer[mlPointer++] = num >> 8 & 0xff;
    mlBuffer[mlPointer++] = num & 0xff;
  }

  function encode32bit(num) {
    TRACE('encode32bit:', num, '->', num >> 24 & 0xff, num >> 16 & 0xff, num >> 8 & 0xff, num & 0xff, 'dsl pointer:', dslPointer, ', ml pointer:', mlPointer);
    ASSERT(typeof num === 'number', 'Encoding 32bit must be num', typeof num, num);
    ASSERT(num >= 0, 'OOB num', num);
    if (num > 0xffffffff) THROW('This requires 64bit support');
    if (mlPointer >= mlBufSize - 3) grow();
    mlBuffer[mlPointer++] = num >> 24 & 0xff;
    mlBuffer[mlPointer++] = num >> 16 & 0xff;
    mlBuffer[mlPointer++] = num >> 8 & 0xff;
    mlBuffer[mlPointer++] = num & 0xff;
  }

  function grow(forcedExtraSpace) {
    TRACE(' - grow(' + (forcedExtraSpace || '') + ') from', mlBufSize); // grow the buffer by 10% or `forcedExtraSpace`
    // you can't really grow existing buffers, instead you create a bigger buffer and copy the old one into it...

    var oldSize = mlBufSize;
    if (forcedExtraSpace) mlBufSize += forcedExtraSpace;else mlBufSize += Math.max(Math.ceil(mlBufSize * 0.1), 10);
    ASSERT(mlBufSize > mlBuffer.length, 'grow() should grow() at least a bit...', mlBuffer.length, '->', mlBufSize);

    if (typeof Buffer === 'undefined') {
      if (ArrayBuffer.transfer) mlBuffer = new Uint8Array(ArrayBuffer.transfer(mlBuffer.buffer, mlBufSize));else mlBuffer = new Uint8Array(ArrayBufferTransferPoly(mlBuffer.buffer, mlBufSize));
    } else {
      mlBuffer = new Uint8Array(Buffer.concat([mlBuffer], mlBufSize)); // Wont actually concat, but will copy the existing buffer into a buffer of given size

      mlBuffer.fill(0, oldSize);
    }

    ASSERT(mlBuffer instanceof Uint8Array);
  }

  function read() {
    return dslBuf[dslPointer];
  }

  function readD(delta) {
    return dslBuf[dslPointer + delta];
  }

  function substr_expensive(start, stop) {
    // Use sparingly!
    return String.fromCharCode.apply(String, dslBuf.slice(start, stop));
  }

  function skip() {
    ++dslPointer;
  }

  function is(c, desc) {
    if (!desc) desc = '';
    if (read() !== c) THROW('Expected ' + desc + ' `' + c + '`, found `' + read() + '`');
    skip();
  }

  function skipWhitespaces() {
    while (dslPointer < len && isWhitespace(read())) {
      skip();
    }
  }

  function skipWhites() {
    while (!isEof()) {
      var c = read();

      if (isWhite(c)) {
        skip();
      } else if (isComment(c)) {
        skipComment();
      } else {
        break;
      }
    }
  }

  function isWhitespace(s) {
    // Make sure you dont actually want isNewlineChar()
    return s === $$SPACE || s === $$TAB;
  }

  function isNewlineChar(s) {
    return s === $$CR || s === $$LF;
  }

  function atEol(c) {
    return isNewlineChar(c) || isComment(c) || isEof();
  }

  function isLineEnd(s) {
    // The line ends at a newline or a comment
    return s === $$CR || s === $$LF || s === $$HASH;
  }

  function isComment(s) {
    return s === $$HASH;
  }

  function isWhite(s) {
    return isWhitespace(s) || isNewlineChar(s);
  }

  function expectEol() {
    skipWhitespaces();

    if (dslPointer < len) {
      var c = read();

      if (c === $$HASH) {
        skipComment();
      } else if (isNewlineChar(c)) {
        skip();
      } else {
        THROW('Expected EOL but got `' + read() + '`');
      }
    }
  }

  function isEof() {
    return dslPointer >= len;
  }

  function parseStatement() {
    // Either:
    // - start with colon: var decl
    // - start with hash: line comment
    // - empty: empty
    // - otherwise: constraint
    skipWhites();
    ASSERT(read() !== $$HASH, 'comments should be parsed by skipWhites');

    switch (read()) {
      case $$COLON:
        parseVar();
        return;

      case $$AT:
        parseAtRule();
        return;

      default:
        if (!isEof()) {
          parseVoidConstraint();
        }

    }
  }

  function parseVar() {
    skip(); // Already is($$COLON)

    skipWhitespaces();
    var nameNames = parseIdentifier();
    skipWhitespaces();

    if (read() === $$COMMA) {
      nameNames = [nameNames];

      do {
        skip();
        skipWhitespaces();
        nameNames.push(parseIdentifier());
        skipWhitespaces();
      } while (!isEof() && read() === $$COMMA);
    }

    if (read() === $$EQ) {
      skip();
      skipWhitespaces();
    }

    var domain = parseDomain();
    skipWhitespaces();
    var mod = parseModifier();
    expectEol();

    if (typeof nameNames === 'string') {
      addParsedVar(nameNames, domain, mod);
    } else {
      nameNames.forEach(function (name) {
        return addParsedVar(name, domain, mod);
      });
    }
  }

  function addParsedVar(name, domain, mod) {
    return addVar(name, domain, mod, false, true, THROW);
  }

  function parseIdentifier() {
    if (read() === $$SQUOTE) return parseQuotedIdentifier();
    return parseUnquotedIdentifier();
  }

  function parseQuotedIdentifier() {
    is($$SQUOTE);
    var ident = '';

    while (!isEof()) {
      var c = read();
      if (c === $$SQUOTE) break;
      if (c !== $$HASH && isLineEnd(c)) THROW('Quoted identifier wasnt closed at eol');
      ident += String.fromCharCode(c);
      skip();
    }

    if (isEof()) THROW('Quoted identifier wasnt closed at eof');
    if (!ident) THROW('Expected to parse identifier, found none');
    skip(); // Quote

    return ident; // Return unquoted ident
  }

  function parseUnquotedIdentifier() {
    // Anything terminated by whitespace
    var c = read();
    var ident = '';
    if (c >= $$0 && c <= $$9) THROW('Unquoted ident cant start with number');

    while (!isEof()) {
      c = read();
      if (!isValidUnquotedIdentChar(c)) break;
      ident += String.fromCharCode(c);
      skip();
    }

    if (!ident) THROW('Expected to parse identifier, found none');
    return ident;
  }

  function isValidUnquotedIdentChar(c) {
    switch (c) {
      case $$LEFTPAREN:
      case $$RIGHTPAREN:
      case $$COMMA:
      case $$LEFTBRACK:
      case $$RIGHTBRACK:
      case $$SQUOTE:
      case $$HASH:
        return false;
    }

    if (isWhite(c)) return false;
    return true;
  }

  function parseDomain() {
    // []
    // [lo hi]
    // [[lo hi] [lo hi] ..]
    // *
    // 25
    // (comma's optional and ignored)
    var domain;
    var c = read();

    switch (c) {
      case $$LEFTBRACK:
        is($$LEFTBRACK, 'domain start');
        skipWhitespaces();
        domain = [];

        if (read() === $$LEFTBRACK) {
          // Range inside the domain that is wrapped in brakcets
          do {
            skip();
            skipWhitespaces();
            var lo = parseNumber();
            skipWhitespaces();

            if (read() === $$COMMA) {
              skip();
              skipWhitespaces();
            }

            var hi = parseNumber();
            skipWhitespaces();
            is($$RIGHTBRACK, 'range-end');
            skipWhitespaces();
            domain.push(lo, hi);

            if (read() === $$COMMA) {
              skip();
              skipWhitespaces();
            }
          } while (read() === $$LEFTBRACK);
        } else {
          // Individual ranges not wrapped
          while (read() !== $$RIGHTBRACK) {
            skipWhitespaces();

            var _lo = parseNumber();

            skipWhitespaces();

            if (read() === $$COMMA) {
              skip();
              skipWhitespaces();
            }

            var _hi = parseNumber();

            skipWhitespaces();
            domain.push(_lo, _hi);

            if (read() === $$COMMA) {
              skip();
              skipWhitespaces();
            }
          }
        }

        is($$RIGHTBRACK, 'domain-end');
        if (domain.length === 0) THROW('Empty domain [] in dsl, this problem will always reject');
        return domain;

      case $$STAR:
        skip();
        return [SUB, SUP];

      case $$0:
      case $$1:
      case $$2:
      case $$3:
      case $$4:
      case $$5:
      case $$6:
      case $$7:
      case $$8:
      case $$9:
        var v = parseNumber();
        skipWhitespaces();
        return [v, v];
    }

    THROW('Expecting valid domain start, found `' + c + '`');
  }

  function parseModifier() {
    if (read() !== $$AT) return;
    skip();
    var mod = {};
    var stratName = '';

    while (true) {
      var c = read();
      if (!(c >= $$a && c <= $$z || c >= $$A && c <= $$Z)) break;
      stratName += String.fromCharCode(c);
      skip();
    }

    switch (stratName) {
      case 'list':
        parseList(mod);
        break;

      case 'markov':
        parseMarkov(mod);
        break;

      case 'max':
      case 'mid':
      case 'min':
      case 'naive':
        mod.valtype = stratName;
        break;

      case 'minMaxCycle':
      case 'splitMax':
      case 'splitMin':
        THROW('TODO: implement this modifier [' + stratName + ']');
        break;

      default:
        THROW('implement me (var mod) [`' + stratName + '`]');
    }

    mod.valtype = stratName;
    return mod;
  }

  function parseList(mod) {
    skipWhitespaces();

    if (!(readD(0) === $$p && readD(1) === $$r && readD(2) === $$i && readD(3) === $$o && readD(4) === $$LEFTPAREN)) {
      THROW('Expecting the priorities to follow the `@list`');
    }

    dslPointer += 5;
    mod.valtype = 'list';
    mod.list = parseNumList();
    is($$RIGHTPAREN, 'list end');
  }

  function parseMarkov(mod) {
    mod.valtype = 'markov';
    var repeat = true;

    while (repeat) {
      repeat = false;
      skipWhitespaces();

      switch (read()) {
        case $$m:
          // Matrix
          if (readD(1) === $$a && readD(2) === $$t && readD(3) === $$r && readD(4) === $$i && readD(5) === $$x && readD(6) === $$LEFTPAREN) {
            // TOFIX: there is no validation here. apply stricter and safe matrix parsing
            dslPointer += 7;
            var start = dslPointer;

            while (read() !== $$RIGHTPAREN && !isEof()) {
              skip();
            }

            if (isEof()) THROW('The matrix must be closed by a `)` but did not find any');
            ASSERT(read() === $$RIGHTPAREN, 'code should only stop at eof or )');
            var matrix = substr_expensive(start, dslPointer);
            var code = 'return ' + matrix;
            var func = new Function(code);
            /* eslint no-new-func: "off" */

            mod.matrix = func();
            is($$RIGHTPAREN, 'end of matrix'); // Kind of a redundant double check. could also just skip() here.

            repeat = true;
          }

          break;

        case $$l:
          // Legend
          if (readD(1) === $$e && readD(2) === $$g && readD(3) === $$e && readD(4) === $$n && readD(5) === $$d && readD(6) === $$LEFTPAREN) {
            dslPointer += 7;
            skipWhitespaces();
            mod.legend = parseNumList();
            skipWhitespaces();
            is($$RIGHTPAREN, 'legend closer');
            repeat = true;
          }

          break;

        case $$e:
          // Expand
          if (readD(1) === $$x && readD(2) === $$p && readD(3) === $$a && readD(4) === $$n && readD(5) === $$d && readD(6) === $$LEFTPAREN) {
            dslPointer += 7;
            skipWhitespaces();
            mod.expandVectorsWith = parseNumber();
            skipWhitespaces();
            is($$RIGHTPAREN, 'expand closer');
            repeat = true;
          }

          break;
      }
    }
  }

  function skipComment() {
    is($$HASH, 'comment start'); // is('#', 'comment hash');

    while (!isEof() && !isNewlineChar(read())) {
      skip();
    }

    if (!isEof()) skip();
  }

  function parseVoidConstraint() {
    // Parse a constraint that does not return a value itself
    // first try to parse single value constraints without value like markov() and diff()
    if (parseUexpr()) return; // So the first value must be a value returning expr

    parseComplexVoidConstraint();
    expectEol();
  }

  function parseComplexVoidConstraint() {
    // Parse a constraint that at least starts with a Vexpr but ultimately doesnt return anything
    var indexA = parseVexpr(undefined, true);
    skipWhitespaces(); // `A==B<eof>` then A==B would be part of A and the parser would want to parse a cop here. there's a test case.

    if (isEof()) THROW('Expected to parse a cop but reached eof instead');
    var cop = parseCop();
    skipWhitespaces();

    if (cop === '=') {
      lastAssignmentIndex = indexA;
      parseAssignment(indexA);
    } else {
      ASSERT(cop, 'the cop parser should require to parse a valid cop');
      var indexB = parseVexpr();
      compileVoidConstraint(indexA, cop, indexB);
    }
  }

  function compileVoidConstraint(indexA, cop, indexB) {
    switch (cop) {
      case '==':
        startConstraint(ML_SAME);
        encode16bit(2);
        encode16bit(indexA < indexB ? indexA : indexB);
        encode16bit(indexA < indexB ? indexB : indexA);
        break;

      case '!=':
        startConstraint(ML_DIFF);
        encode16bit(2);
        encode16bit(indexA < indexB ? indexA : indexB);
        encode16bit(indexA < indexB ? indexB : indexA);
        break;

      case '<':
        startConstraint(ML_LT);
        encode16bit(2);
        encode16bit(indexA);
        encode16bit(indexB);
        break;

      case '<=':
        startConstraint(ML_LTE);
        encode16bit(2);
        encode16bit(indexA);
        encode16bit(indexB);
        break;

      case '>':
        startConstraint(ML_LT);
        encode16bit(2);
        encode16bit(indexB);
        encode16bit(indexA);
        break;

      case '>=':
        startConstraint(ML_LTE);
        encode16bit(2);
        encode16bit(indexB);
        encode16bit(indexA);
        break;

      case '&':
        startConstraint(ML_ALL);
        encode16bit(2);
        encode16bit(indexA < indexB ? indexA : indexB);
        encode16bit(indexA < indexB ? indexB : indexA);
        break;

      case '!&':
        startConstraint(ML_NALL);
        encode16bit(2);
        encode16bit(indexA < indexB ? indexA : indexB);
        encode16bit(indexA < indexB ? indexB : indexA);
        break;

      case '|':
        startConstraint(ML_SOME);
        encode16bit(2);
        encode16bit(indexA < indexB ? indexA : indexB);
        encode16bit(indexA < indexB ? indexB : indexA);
        break;

      case '!|':
        startConstraint(ML_NONE);
        encode16bit(2);
        encode16bit(indexA < indexB ? indexA : indexB);
        encode16bit(indexA < indexB ? indexB : indexA);
        break;

      case '^':
        startConstraint(ML_XOR);
        encode16bit(2); // This brings the op size in line with all other ops. kind of a waste but so be it.

        encode16bit(indexA < indexB ? indexA : indexB);
        encode16bit(indexA < indexB ? indexB : indexA);
        break;

      case '!^':
        startConstraint(ML_XNOR);
        encode16bit(2);
        encode16bit(indexA < indexB ? indexA : indexB);
        encode16bit(indexA < indexB ? indexB : indexA);
        break;

      case '->':
        startConstraint(ML_IMP);
        encode16bit(2);
        encode16bit(indexA);
        encode16bit(indexB);
        break;

      case '!->':
        startConstraint(ML_NIMP);
        encode16bit(2);
        encode16bit(indexA);
        encode16bit(indexB);
        break;

      default:
        THROW('Unknown constraint op: [' + cop + ']');
    }
  }

  function parseAssignment(indexC) {
    var indexA = parseVexpr(indexC);
    skipWhitespaces();
    var c = read();

    if (isEof() || isLineEnd(c)) {
      // Any var, literal, or group without "top-level" op (`A=5`, `A=X`, `A=(B+C)`, `A=sum(...)`, etc)
      if (indexA !== indexC) {
        compileVoidConstraint(indexA, '==', indexC);
      }
    } else {
      var rop = parseRop();
      if (!rop) THROW('Expecting right paren or rop, got [' + rop + ']');
      skipWhitespaces();
      var indexB = parseVexpr();
      return compileValueConstraint(indexA, rop, indexB, indexC);
    }
  }

  function compileValueConstraint(indexA, rop, indexB, indexC) {
    var wasReifier = false;

    switch (rop) {
      case '==?':
        startConstraint(ML_ISSAME);
        encode16bit(2);
        encode16bit(indexA < indexB ? indexA : indexB);
        encode16bit(indexA < indexB ? indexB : indexA);
        encode16bit(indexC);
        wasReifier = true;
        break;

      case '!=?':
        startConstraint(ML_ISDIFF);
        encode16bit(2);
        encode16bit(indexA < indexB ? indexA : indexB);
        encode16bit(indexA < indexB ? indexB : indexA);
        encode16bit(indexC);
        wasReifier = true;
        break;

      case '<?':
        startConstraint(ML_ISLT);
        encode16bit(indexA);
        encode16bit(indexB);
        encode16bit(indexC);
        wasReifier = true;
        break;

      case '<=?':
        startConstraint(ML_ISLTE);
        encode16bit(indexA);
        encode16bit(indexB);
        encode16bit(indexC);
        wasReifier = true;
        break;

      case '&?':
        startConstraint(ML_ISALL);
        encode16bit(2);
        encode16bit(indexA);
        encode16bit(indexB);
        encode16bit(indexC);
        break;

      case '!&?':
        startConstraint(ML_ISNALL);
        encode16bit(2);
        encode16bit(indexA);
        encode16bit(indexB);
        encode16bit(indexC);
        break;

      case '|?':
        startConstraint(ML_ISSOME);
        encode16bit(2);
        encode16bit(indexA);
        encode16bit(indexB);
        encode16bit(indexC);
        break;

      case '!|?':
        startConstraint(ML_ISNONE);
        encode16bit(2);
        encode16bit(indexA);
        encode16bit(indexB);
        encode16bit(indexC);
        break;

      case '+':
        startConstraint(ML_SUM);
        encode16bit(2); // Count

        encode16bit(indexA < indexB ? indexA : indexB);
        encode16bit(indexA < indexB ? indexB : indexA);
        encode16bit(indexC);
        break;

      case '-':
        startConstraint(ML_MINUS);
        encode16bit(indexA);
        encode16bit(indexB);
        encode16bit(indexC);
        break;

      case '*':
        startConstraint(ML_PRODUCT);
        encode16bit(2);
        encode16bit(indexA < indexB ? indexA : indexB);
        encode16bit(indexA < indexB ? indexB : indexA);
        encode16bit(indexC);
        break;

      case '/':
        startConstraint(ML_DIV);
        encode16bit(indexA);
        encode16bit(indexB);
        encode16bit(indexC);
        break;

      case '>?':
        return compileValueConstraint(indexB, '<?', indexA, indexC);

      case '>=?':
        return compileValueConstraint(indexB, '<=?', indexA, indexC);

      default:
        THROW('Expecting right paren or rop, got [' + rop + ']');
    }

    if (wasReifier && indexC === lastAssignmentIndex && indexC === lastUnknownIndex) setDomain(indexC, domain_createRange(0, 1));
    return indexC;
  }

  function parseCop() {
    var c = read();

    switch (c) {
      case $$EQ:
        skip();

        if (read() === $$EQ) {
          skip();
          return '==';
        }

        return '=';

      case $$BANG:
        skip();
        var r = read();

        if (r === $$EQ) {
          skip();
          return '!=';
        }

        if (r === $$AND) {
          skip();
          return '!&';
        }

        if (r === $$XOR) {
          skip();
          return '!^';
        }

        if (r === $$OR) {
          skip();
          return '!|';
        }

        if (r === $$DASH && readD(1) === $$GT) {
          skip();
          skip();
          return '!->';
        }

        return THROW('Unknown cop that starts with [!]');

      case $$LT:
        skip();

        if (read() === $$EQ) {
          skip();
          return '<=';
        }

        return '<';

      case $$GT:
        skip();

        if (read() === $$EQ) {
          skip();
          return '>=';
        }

        return '>';

      case $$DASH:
        if (readD(1) === $$GT) {
          skip();
          skip();
          return '->';
        }

        break;
      // Error

      case $$AND:
        skip();
        return '&';

      case $$OR:
        skip();
        return '|';

      case $$XOR:
        skip();
        return '^';

      case $$HASH:
        return THROW('Expected to parse a cop but found a comment instead');
    }

    if (isEof()) THROW('Expected to parse a cop but reached eof instead');
    THROW('Unknown cop char: `' + c + '`');
  }

  function parseRop() {
    switch (read()) {
      case $$EQ:
        skip();

        if (read() === $$EQ) {
          skip();
          is($$QM, 'reifier suffix');
          return '==?';
        }

        return '=';

      case $$BANG:
        skip();
        var r = '';

        if (read() === $$EQ) {
          is($$EQ, 'middle part of !=? op');
          r = '!=?';
        } else if (read() === $$AND) {
          is($$AND, 'middle part of !&? op');
          r = '!&?';
        } else if (read() === $$OR) {
          is($$OR, 'middle part of !|? op');
          r = '!|?';
        } else {
          THROW('invalid rop that starts with a bang');
        }

        is($$QM, 'reifier suffix');
        return r;

      case $$LT:
        skip();

        if (read() === $$EQ) {
          skip();
          is($$QM, 'reifier suffix');
          return '<=?';
        }

        is($$QM, 'reifier suffix');
        return '<?';

      case $$GT:
        skip();

        if (read() === $$EQ) {
          skip();
          is($$QM, 'reifier suffix');
          return '>=?';
        }

        is($$QM, 'reifier suffix');
        return '>?';

      case $$OR:
        skip();
        is($$QM, 'issome suffix');
        return '|?';

      case $$AND:
        skip();
        is($$QM, 'isall suffix');
        return '&?';

      case $$PLUS:
        skip();
        return '+';

      case $$DASH:
        skip();
        return '-';

      case $$STAR:
        skip();
        return '*';

      case $$DIV:
        skip();
        return '/';

      default:
        return '';
    }
  }

  function parseUexpr() {
    // It's not very efficient (we could parse an ident before and check that result here) but it'll work for now
    var c = read(); // Distinct is legacy support, same as diff()

    if (c === $$d && readD(1) === $$i && readD(2) === $$s && readD(3) === $$t && readD(4) === $$i && readD(5) === $$n && readD(6) === $$c && readD(7) === $$t && readD(8) === $$LEFTPAREN) {
      parseCalledListConstraint(ML_DIFF, 9);
      return true;
    }

    if (c === $$d && readD(1) === $$i && readD(2) === $$f && readD(3) === $$f && readD(4) === $$LEFTPAREN) {
      parseCalledListConstraint(ML_DIFF, 5);
      return true;
    }

    if (c === $$a && readD(1) === $$l && readD(2) === $$l && readD(3) === $$LEFTPAREN) {
      parseCalledListConstraint(ML_ALL, 4);
      return true;
    }

    if (c === $$n && readD(1) === $$a && readD(2) === $$l && readD(3) === $$l && readD(4) === $$LEFTPAREN) {
      parseCalledListConstraint(ML_NALL, 5);
      return true;
    }

    if (c === $$s && readD(1) === $$a && readD(2) === $$m && readD(3) === $$e && readD(4) === $$LEFTPAREN) {
      parseCalledListConstraint(ML_SAME, 5);
      return true;
    }

    if (c === $$s && readD(1) === $$o && readD(2) === $$m && readD(3) === $$e && readD(4) === $$LEFTPAREN) {
      parseCalledListConstraint(ML_SOME, 5);
      return true;
    }

    if (c === $$n && readD(1) === $$o && readD(2) === $$n && readD(3) === $$e && readD(4) === $$LEFTPAREN) {
      parseCalledListConstraint(ML_NONE, 5);
      return true;
    }

    if (c === $$x && readD(1) === $$n && readD(2) === $$o && readD(3) === $$r && readD(4) === $$LEFTPAREN) {
      parseCalledListConstraint(ML_XNOR, 5);
      return true;
    }

    return false;
  }

  function parseCalledListConstraint(opcode, delta) {
    dslPointer += delta;
    skipWhitespaces();
    var vals = parseVexpList();
    ASSERT(vals.length <= 255, 'dont do lists with more than 255 vars :(');
    startConstraint(opcode);
    encode16bit(vals.length);
    vals.forEach(encode16bit);
    skipWhitespaces();
    is($$RIGHTPAREN, 'parseCalledListConstraint call closer');
    expectEol();
  }

  function parseVexpList() {
    var list = [];
    skipWhitespaces();

    while (!isEof() && read() !== $$RIGHTPAREN) {
      var index = parseVexpr();
      list.push(index);
      skipWhitespaces();

      if (read() === $$COMMA) {
        skip();
        skipWhitespaces();
      }
    }

    if (!list.length) THROW('Expecting at least one expression in the list');
    return list;
  }

  function parseVexpr(resultIndex, canBeUnknown) {
    // Types: valcall, ident, number, group
    // ALWAYS return a var or constant INDEX!
    // resultIndex is only passed on if this was an explicit
    // assignment (like the index of `X` in `X = sum(A B C)`)
    var c = read();
    var index;

    if (c >= $$0 && c <= $$9) {
      var num = parseNumber();
      index = addVar(undefined, num, false, false, true);
    } else if (c === $$LEFTPAREN) {
      index = parseGrouping();
    } else if (c === $$LEFTBRACK) {
      var domain = parseDomain();
      index = addVar(undefined, domain, false, false, true);
    } else {
      var ident = parseIdentifier();

      if (read() === $$LEFTPAREN) {
        if (ident === 'sum') index = parseArgs(ML_SUM, resultIndex, false);else if (ident === 'product') index = parseArgs(ML_PRODUCT, resultIndex, false);else if (ident === 'all?') index = parseArgs(ML_ISALL, resultIndex, true);else if (ident === 'diff?') index = parseArgs(ML_ISDIFF, resultIndex, true);else if (ident === 'nall?') index = parseArgs(ML_ISNALL, resultIndex, true);else if (ident === 'none?') index = parseArgs(ML_ISNONE, resultIndex, true);else if (ident === 'same?') index = parseArgs(ML_ISSAME, resultIndex, true);else if (ident === 'some?') index = parseArgs(ML_ISSOME, resultIndex, true);else THROW('Unknown reifier constraint func: ' + ident);
      } else {
        // Implicitly declare unknown vars as [SUB,SUP]
        index = name2index(ident, false, true);

        if (index < 0) {
          if (canBeUnknown) lastUnknownIndex = index = addVar(ident, undefined, false, false, true);else THROW('CONSTRAINT_VARS_SHOULD_BE_DECLARED; Unknown var [' + ident + ']');
        }
      }
    }

    TRACE('parseVexpr resulted in index:', index);
    return index;
  }

  function parseGrouping() {
    is($$LEFTPAREN, 'group open');
    skipWhitespaces();
    var indexA = parseVexpr();
    skipWhitespaces(); // Just wrapping a vexpr is okay, otherwise it needs a rop

    if (read() !== $$RIGHTPAREN) {
      var rop = parseRop();
      if (!rop) THROW('Expecting right paren or rop');
      skipWhitespaces();
      var indexB = parseVexpr();
      var indexC = addVar(undefined, rop[rop.length - 1] === '?' ? [0, 1] : undefined, false, false, true);
      indexA = compileValueConstraint(indexA, rop, indexB, indexC);
      skipWhitespaces();
    }

    is($$RIGHTPAREN, 'group closer');
    return indexA;
  }

  function parseNumber() {
    var numstr = parseNumstr();

    if (!numstr) {
      THROW('Expecting to parse a number but did not find any digits c=[ord(' + read() + ')=' + String.fromCharCode(read()) + ']');
    }

    return parseInt(numstr, 10);
  }

  function parseArgs(op, resultIndex, defaultBoolResult) {
    is($$LEFTPAREN, 'args call opener');
    skipWhitespaces();
    var refs = parseVexpList(); // Note: the var may not declared if the constraint was anonymously grouped (ie `(sum(A B)>10)`)

    if (resultIndex === undefined) resultIndex = addVar(undefined, defaultBoolResult ? [0, 1] : undefined, false, false, true);else if (resultIndex === lastAssignmentIndex && resultIndex === lastUnknownIndex && defaultBoolResult) setDomain(resultIndex, domain_createRange(0, 1));
    TRACE('parseArgs refs:', resultIndex, ' = all(', refs, '), defaultBoolResult:', defaultBoolResult);
    startConstraint(op);
    encode16bit(refs.length); // Count

    refs.sort(function (a, b) {
      return a - b;
    });
    refs.forEach(encode16bit);
    encode16bit(resultIndex);
    skipWhitespaces();
    is($$RIGHTPAREN, 'args closer');
    return resultIndex;
  }

  function parseNumstr() {
    var numstr = '';

    while (!isEof()) {
      var c = read();
      if (c < $$0 || c > $$9) break;
      numstr += String.fromCharCode(c);
      skip();
    }

    return numstr;
  }

  function parseNumList() {
    var nums = [];
    skipWhitespaces();
    var numstr = parseNumstr();

    while (numstr) {
      nums.push(parseInt(numstr, 10));
      skipWhitespaces();

      if (read() === $$COMMA) {
        ++dslPointer;
        skipWhitespaces();
      }

      numstr = parseNumstr();
    }

    if (!nums.length) THROW('Expected to parse a list of at least some numbers but found none');
    return nums;
  }

  function parseIdentsTo(target) {
    var idents = parseIdents(target);
    if (!idents.length) THROW('Expected to parse a list of at least some identifiers but found none');
    return idents;
  }

  function parseIdents(target) {
    var idents = [];
    skipWhitespaces();

    while (!isEof()) {
      var c = read();
      if (c === target) return idents;
      if (isLineEnd(c)) break;

      if (c === $$COMMA) {
        if (!idents.length) THROW('Leading comma not supported');
        skip();
        skipWhitespaces();
        if (atEol(read())) THROW('Trailing comma not supported'); // Mmmm or should we? dont believe it to be relevant for this language

        c = read();
        if (c === $$COMMA) THROW('Double comma not supported');
      }

      var ident = parseIdentifier();
      idents.push(ident);
      skipWhitespaces();
    }

    if (target === undefined) return idents;
    THROW('Missing target char at eol/eof');
  }

  function readLineRest() {
    var str = '';

    while (!isEof()) {
      var c = read();
      if (isNewlineChar(c)) break;
      str += String.fromCharCode(c);
      skip();
    }

    return str;
  }

  function parseAtRule() {
    is($$AT); // Mostly temporary hacks while the dsl stabilizes...

    var ruleName = parseIdentifier();

    if (ruleName === 'custom') {
      skipWhitespaces();
      var ident = parseIdentifier();
      skipWhitespaces();

      if (read() === $$EQ) {
        skip();
        skipWhitespaces();
      }

      switch (ident) {
        case 'var-strat':
          parseVarStrat();
          break;

        case 'val-strat':
          parseValStrat();
          break;

        case 'set-valdist':
          skipWhitespaces();
          var target = parseIdentifier();
          var config = parseRestCustom();
          setValDist(name2index(target, true), JSON.parse(config));
          break;

        case 'noleaf':
          {
            skipWhitespaces();
            var idents = parseIdentsTo(undefined);

            for (var i = 0, _len = idents.length; i < _len; ++i) {
              // Debug vars are never considered leaf vars until we change that (to something else and update this to something that still does the same thing)
              // this is for testing as a simple tool to prevent many trivial optimizations to kick in. it's not flawless.
              // encode 3x to artificially inflate the count beyond most tricks
              // these should not be deduped... but keep in mind that a noleafed alias gets double the counts
              var index = name2index(idents[i]);

              for (var j = 0; j < 3; ++j) {
                encode8bit(ML_NOLEAF);
                encode16bit(index);
              }
            }

            break;
          }

        case 'nobool':
          {
            // Debugging tool; bounty should consider this var a non-booly regardless of whether it actually is
            skipWhitespaces();

            var _idents = parseIdentsTo(undefined);

            for (var _i = 0, _len2 = _idents.length; _i < _len2; ++_i) {
              var _index = name2index(_idents[_i]);

              encode8bit(ML_NOBOOL);
              encode16bit(_index);
            }

            break;
          }

        case 'free':
          skipWhitespaces();
          var size = parseNumber();
          TRACE('Found a jump of', size);
          freeDirective = size;
          break;

        case 'targets':
          parseTargets();
          break;

        default:
          THROW('Unsupported custom rule: ' + ident);
      }
    } else {
      THROW('Unknown atrule [' + ruleName + ']');
    }

    expectEol();
  }

  function setValDist(varIndex, dist) {
    ASSERT(typeof varIndex === 'number', 'expecting var indexes');
    ASSERT(problem.valdist[varIndex] === undefined, 'not expecting valdists to be set twice for the same var');
    problem.valdist[varIndex] = dist;
  }

  function compileJump(size) {
    TRACE('compileJump(' + size + '), mlPointer=', mlPointer);
    ASSERT(size > 0, 'dont call this function on size=0');

    switch (size) {
      case 0:
        // Dead code. test code should catch these cases at call site. runtime can still just ignore it.
        break;
      // ignore. only expliclty illustrates no free space

      case 1:
        encode8bit(ML_NOOP);
        break;

      case 2:
        encode8bit(ML_NOOP2);
        encode8bit(0);
        break;

      case 3:
        encode8bit(ML_NOOP3);
        encode8bit(0);
        encode8bit(0);
        break;

      case 4:
        encode8bit(ML_NOOP4);
        encode8bit(0);
        encode8bit(0);
        encode8bit(0);
        break;

      default:
        // because we manually update mlPointer the buffer may not grow accordingly. so do that immediately
        // but only if necessary
        var jumpDestination = mlPointer + size;

        if (mlBufSize <= jumpDestination) {
          var sizeDifference = jumpDestination - mlBufSize;
          var growAmount = jumpDestination / 10 | 0 + sizeDifference;
          grow(growAmount);
        }

        if (size < 0xffff) {
          encode8bit(ML_JMP);
          encode16bit(size - SIZEOF_V);
          mlPointer += size - SIZEOF_V;
        } else {
          encode8bit(ML_JMP32);
          encode32bit(size - SIZEOF_W);
          mlPointer += size - SIZEOF_W;
        }

      // Buffer is explicitly fill(0)'d so no need to clear it out here (otherwise we probably should)
    }
  }

  function parseVarStrat() {
    // @custom var-strat [fallback] [=] naive
    // @custom var-strat [fallback] [=] size
    // @custom var-strat [fallback] [=] min
    // @custom var-strat [fallback] [=] max
    // @custom var-strat [fallback] [=] throw
    // @custom var-strat [fallback] [inverted] [list] (a b c)
    var fallback = false; // List only

    var inverted = false; // List only

    var issed = false; // Had equal sign (illegal for list)

    if (read() === $$f) {
      var ident = parseIdentifier();
      if (ident !== 'fallback') THROW('Expecting var strat name, found [' + ident + ']');
      fallback = true;
      skipWhitespaces();
    }

    if (read() === $$i) {
      var _ident = parseIdentifier();

      if (_ident !== 'inverted') THROW('Expecting var strat name, found [' + _ident + ']');
      inverted = true;
      skipWhitespaces();
    }

    if (read() === $$EQ) {
      skip();
      issed = true;
      skipWhitespaces();
    }

    if (read() === $$LEFTPAREN) {
      parseVarStratList(fallback, inverted);
    } else {
      var _ident2 = parseIdentifier();

      if (_ident2 === 'naive' || _ident2 === 'size' || _ident2 === 'min' || _ident2 === 'max' || _ident2 === 'throw') {
        if (inverted) THROW('The `inverted` keyword is only used with a list');

        if (fallback) {
          addFallbackToVarStrat(_ident2);
        } else {
          problem.input.varstrat = _ident2;
        }
      } else if (_ident2 === 'list') {
        skipWhitespaces();
        if (issed) THROW('The `=` should not be used for a list');
        if (read() !== $$LEFTPAREN) THROW('Expecting list of idents now');
        parseVarStratList(fallback, inverted);
      } else {
        THROW('Unknown var strat [' + _ident2 + ']');
      }
    }

    skipWhitespaces();
  }

  function parseVarStratList(fallback, inverted) {
    is($$LEFTPAREN, 'List open');
    skipWhitespaces();
    var idents = parseIdents($$RIGHTPAREN);
    skipWhitespaces();
    is($$RIGHTPAREN, 'List must be closed');
    var strat = {
      type: 'list',
      inverted: inverted,
      priorityByName: idents
    };

    if (fallback) {
      addFallbackToVarStrat(strat);
    } else {
      problem.input.varstrat = strat;
    }
  }

  function addFallbackToVarStrat(strat) {
    var vs = problem.input.varstrat;
    ASSERT(vs, 'should set the var strat before declaring its backup'); // Should we just throw for this?

    if (typeof vs === 'string') vs = problem.input.varstrat = {
      type: vs
    };

    while (vs.fallback) {
      if (typeof vs.fallback === 'string') {
        vs = vs.fallback = {
          type: vs.fallback
        };
      } else {
        vs = vs.fallback;
      }
    }

    vs.fallback = strat;
  }

  function parseValStrat() {
    problem.input.valstrat = parseIdentifier();
  }

  function parseRestCustom() {
    skipWhitespaces();

    if (read() === $$EQ) {
      skip();
      skipWhitespaces();
    }

    return readLineRest();
  }

  function parseTargets() {
    skipWhitespaces();
    if (read() === $$EQ) THROW('Unexpected double eq sign');

    if (read() === $$a && readD(1) === $$l && readD(2) === $$l) {
      dslPointer += 3;
    } else {
      is($$LEFTPAREN, 'ONLY_USE_WITH_SOME_TARGET_VARS; The @targets left-paren');
      var list = parseIdentsTo($$RIGHTPAREN);
      problem.freezeTargets(list);
      is($$RIGHTPAREN, 'The @targets right-paren');
    }

    expectEol();
  }

  function THROW(msg) {
    if (_debug) {
      TRACE(String.fromCharCode.apply(String, dslBuf.slice(0, dslPointer)) + '##|PARSER_IS_HERE[' + msg + ']|##' + String.fromCharCode.apply(String, dslBuf.slice(dslPointer)));
    }

    msg += ', source at ' + dslPointer + ' #|#: `' + String.fromCharCode.apply(String, dslBuf.slice(Math.max(0, dslPointer - 20), dslPointer)) + '#|#' + String.fromCharCode.apply(String, dslBuf.slice(dslPointer, Math.min(dslBuf.length, dslPointer + 20))) + '`';
    throw new Error(msg);
  }
}

function ArrayBufferTransferPoly(source, length) {
  // C/p https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/ArrayBuffer/transfer
  if (!(source instanceof ArrayBuffer)) throw new TypeError('Source must be an instance of ArrayBuffer');
  if (length <= source.byteLength) return source.slice(0, length);
  var sourceView = new Uint8Array(source),
      destView = new Uint8Array(new ArrayBuffer(length));
  destView.set(sourceView);
  return destView.buffer;
}

// Problem optimizer

function min_run(ml, problem, domains, names, firstRun, once) {
  TRACE('min_run, loop:', firstRun, ', byte code:', ml.length < 50 ? ml.join(' ') : '<big>');
  TRACE(ml__debug(ml, 0, 20, problem)); // Now we can access the ml in terms of bytes, jeuj

  var state = min_optimizeConstraints(ml, problem, domains, names, firstRun, once);

  if (state === $SOLVED) {
    TRACE('minimizing solved it!', state); // All constraints have been eliminated
  } else if (state === $REJECTED) {
    TRACE('minimizing rejected it!', state); // An empty domain was found or a literal failed a test
  } else {
    TRACE('pre-optimization finished, not yet solved');
  }

  return state;
}

function min_optimizeConstraints(ml, problem, domains, names, firstRun, once) {
  TRACE('min_optimizeConstraints', ml.length < 50 ? ml.join(' ') : '');
  TRACE(problem.domains.length > 100 ? '' : '  <' + problem.domains.map(function (d, i) {
    return i + ' : ' + problem.varNames[i] + ' : ' + domain__debug(problem.getDomain(i));
  }).join('>, <') + '>');
  TRACE('minimize sweep, ml len=', ml.length, ', firstRun=', firstRun, 'once=', once);
  var varChanged = true;
  var onlyJumps = false;
  var emptyDomain = false;
  var lastPcOffset = 0;
  var lastOp = 0;
  var pc = 0;
  var loops = 0;
  var constraints = 0; // Count a constraint going forward, ignore jumps, reduce when restarting from same pc

  var restartedRelevantOp = false; // Annoying, but restartedRelevantOp could mean more scrubbing is required. but it may not...

  var term = getTerm();
  var addVar = problem.addVar,
      addAlias = problem.addAlias,
      getAlias = problem.getAlias,
      getDomain = problem.getDomain,
      setDomain = problem.setDomain,
      solveStack = problem.solveStack; // Function addPseudoAlias(indexA, indexB, A, B) {
  //  ASSERT(domain_isBoolyPair(A) && domain_isBoolyPair(B), 'assuming A and B are booly pairs');
  //  ASSERT(A !== B, 'booly pairs that are equal are regular aliases so dont call this function on them');
  //
  //  addAlias(indexA, indexB); // A is replaced by B
  //
  //  // consider them aliases but add a special solve stack
  //  // entry to restore the max to A if B turns out nonzero
  //  solveStack.push((_, force, getDomain, setDomain) => {
  //    TRACE(' - deduper psuedo alias; was:', domain__debug(A), '!^', domain__debug(B), ', now:', domain__debug(getDomain(indexA)), '!^', domain__debug(getDomain(indexB)));
  //    let vB = force(indexB);
  //    TRACE(' - B forced to', vB);
  //    if (vB > 0) {
  //      setDomain(indexA, domain_removeValue(A, 0), true, true);
  //    }
  //
  //    ASSERT(getDomain(indexA));
  //    ASSERT(getDomain(indexB));
  //    ASSERT(domain_isSolved(getDomain(indexA)));
  //    ASSERT(domain_isSolved(getDomain(indexB)));
  //    ASSERT((domain_getValue(getDomain(indexA)) === 0) === (domain_getValue(getDomain(indexB)) === 0));
  //  });
  // }

  while (!onlyJumps && (varChanged || restartedRelevantOp)) {
    ++loops; // Term.log('- looping', loops);

    term.time('-> min_loop ' + loops);
    TRACE('min outer loop');
    varChanged = false;
    onlyJumps = true; // Until proven otherwise

    restartedRelevantOp = false;
    pc = 0;
    constraints = 0;
    var ops = min_innerLoop();
    TRACE('changed?', varChanged, 'only jumps?', onlyJumps, 'empty domain?', emptyDomain, 'restartedRelevantOp?', restartedRelevantOp);

    if (emptyDomain) {
      term.log('Empty domain at', lastPcOffset, 'for opcode', lastOp, [ml__debug(ml, lastPcOffset, 1, problem)], ml.slice(lastPcOffset, lastPcOffset + 10));
      term.log('Empty domain, problem rejected');
    }

    term.timeEnd('-> min_loop ' + loops);
    term.log('   - ops this loop:', ops, 'constraints:', constraints);
    if (emptyDomain) return $REJECTED;
    if (onlyJumps) return $SOLVED;
    TRACE('\n## Intermediate state: ##');
    TRACE(ml__debug(ml, 0, 20, problem));
    TRACE(m2d__debug(problem));
    if (once) break;
    firstRun = false;
  }

  if (loops === 1) return $STABLE;
  return $CHANGED; // ####################################################################################

  function readIndex(ml, offset) {
    // Get an index from ml. check for alias, and if so, immediately compile back the alias to improve future fetches.
    var index = ml_dec16(ml, offset);
    var alias = getAlias(index);
    if (alias !== index) ml_enc16(ml, offset, alias);
    return alias;
  }

  function getDomainFast(index) {
    ASSERT(index >= 0 && index <= 0xffff, 'expecting valid index', index);
    ASSERT(getAlias(index) === index, 'index should be unaliased', index, getAlias(index));
    var domain = getDomain(index, true);
    ASSERT(domain, 'domain cant be falsy', domain);
    ASSERT_NORDOM(domain);
    if (!domain) setEmpty(index, 'bad state (empty domain should have been detected sooner)');
    return domain;
  }

  function updateDomain(index, domain, desc) {
    TRACE(' - updateDomain; {', index, '} updated from', domain__debug(getDomain(index)), 'to', domain__debug(domain));
    ASSERT(!domain || domain_intersection(getDomain(index), domain), 'should never add new values to a domain, only remove them', 'index=', index, 'old=', domain__debug(getDomain(index)), 'new=', domain__debug(domain), 'desc=', desc);
    setDomain(index, domain, false, true);

    if (domain) {
      varChanged = true;
    } else {
      TRACE(' - (updateDomain: EMPTY DOMAIN)');
      emptyDomain = true;
    }

    return emptyDomain;
  }

  function setEmpty(index, desc) {
    TRACE(" - :'( setEmpty({", index, '})', desc);
    emptyDomain = true;
    if (index >= 0) updateDomain(index, domain_createEmpty(), 'explicitly empty' + (desc ? '; ' + desc : ''));
  }

  function min_innerLoop() {
    var ops = 0;
    onlyJumps = true;
    var wasMetaOp = false; // Jumps, start, stop, etc. not important if they "change"

    while (pc < ml.length && !emptyDomain) {
      ++ops;
      ++constraints;
      wasMetaOp = false;
      var pcStart = pc;
      lastPcOffset = pc;
      var op = ml[pc];
      lastOp = op; // ASSERT(ml_validateSkeleton(ml, 'min_innerLoop'));

      TRACE(' # CU pc=' + pcStart, ', op=', op, ml__opName(op));
      TRACE(' -> op: ' + ml__debug(ml, pc, 1, problem, true));

      switch (op) {
        case ML_START:
          if (pc !== 0) {
            TRACE('reading a op=zero at position ' + pc + ' which should not happen', ml.slice(Math.max(pc - 100, 0), pc), '<here>', ml.slice(pc, pc + 100));
            return THROW(' ! optimizer problem @', pc);
          }

          wasMetaOp = true;
          ++pc;
          --constraints; // Not a constraint

          break;

        case ML_STOP:
          TRACE(' ! good end @', pcStart);
          wasMetaOp = true;
          --constraints; // Not a constraint

          return ops;

        case ML_LT:
          TRACE('- lt vv @', pcStart);
          min_lt(ml, pc);
          break;

        case ML_LTE:
          TRACE('- lte vv @', pcStart);
          min_lte(ml, pc);
          break;

        case ML_NONE:
          TRACE('- none @', pcStart);
          min_none(ml, pc);
          break;

        case ML_XOR:
          TRACE('- xor @', pcStart);
          min_xor(ml, pc);
          break;

        case ML_XNOR:
          TRACE('- xnor @', pcStart);
          min_xnor(ml, pc);
          break;

        case ML_IMP:
          TRACE('- imp @', pcStart);
          min_imp(ml, pc);
          break;

        case ML_NIMP:
          TRACE('- nimp @', pcStart);
          min_nimp(ml, pc);
          break;

        case ML_DIFF:
          TRACE('- diff @', pcStart);
          min_diff(ml, pc);
          break;

        case ML_ALL:
          TRACE('- all() @', pcStart);
          min_all(ml, pc);
          break;

        case ML_ISDIFF:
          TRACE('- isdiff @', pcStart);
          min_isDiff(ml, pc);
          break;

        case ML_NALL:
          TRACE('- nall @', pcStart);
          min_nall(ml, pc);
          break;

        case ML_SAME:
          TRACE('- same @', pcStart);
          min_same(ml, pc);
          break;

        case ML_SOME:
          TRACE('- some @', pcStart);
          min_some(ml, pc);
          break;

        case ML_ISLT:
          TRACE('- islt vvv @', pcStart);
          min_isLt(ml, pc);
          break;

        case ML_ISLTE:
          TRACE('- islte vvv @', pcStart);
          min_isLte(ml, pc);
          break;

        case ML_ISALL:
          TRACE('- isall @', pcStart);
          min_isAll(ml, pc);
          break;

        case ML_ISNALL:
          TRACE('- isnall @', pcStart);
          min_isNall(ml, pc);
          break;

        case ML_ISSAME:
          TRACE('- issame @', pcStart);
          min_isSame(ml, pc);
          break;

        case ML_ISSOME:
          TRACE('- issome @', pcStart);
          min_isSome(ml, pc);
          break;

        case ML_ISNONE:
          TRACE('- isnone @', pcStart);
          min_isNone(ml, pc);
          break;

        case ML_MINUS:
          TRACE('- minus @', pcStart);
          min_minus(ml, pc);
          break;

        case ML_DIV:
          TRACE('- div @', pcStart);
          min_div(ml, pc);
          break;

        case ML_SUM:
          TRACE('- sum @', pcStart);
          min_sum(ml, pc);
          break;

        case ML_PRODUCT:
          TRACE('- product @', pcStart);
          min_product(ml, pc);
          break;

        case ML_NOBOOL:
          TRACE('- nobool @', pc);
          pc += SIZEOF_V;
          wasMetaOp = true;
          break;

        case ML_NOLEAF:
          TRACE('- noleaf @', pc);
          pc += SIZEOF_V;
          wasMetaOp = true;
          break;

        case ML_NOOP:
          TRACE('- noop @', pc);
          min_moveTo(ml, pc, 1);
          --constraints; // Not a constraint

          wasMetaOp = true;
          break;

        case ML_NOOP2:
          TRACE('- noop2 @', pc);
          min_moveTo(ml, pc, 2);
          --constraints; // Not a constraint

          wasMetaOp = true;
          break;

        case ML_NOOP3:
          TRACE('- noop3 @', pc);
          min_moveTo(ml, pc, 3);
          --constraints; // Not a constraint

          wasMetaOp = true;
          break;

        case ML_NOOP4:
          TRACE('- noop4 @', pc);
          min_moveTo(ml, pc, 4);
          --constraints; // Not a constraint

          wasMetaOp = true;
          break;

        case ML_JMP:
          TRACE('- jmp @', pc);
          min_moveTo(ml, pc, SIZEOF_V + ml_dec16(ml, pc + 1));
          --constraints; // Not a constraint

          wasMetaOp = true;
          break;

        case ML_JMP32:
          TRACE('- jmp32 @', pc);
          min_moveTo(ml, pc, SIZEOF_W + ml_dec32(ml, pc + 1));
          --constraints; // Not a constraint

          wasMetaOp = true;
          break;

        default:
          THROW('(mn) unknown op: 0x' + op.toString(16), ' at', pc);
      }

      if (pc === pcStart && !emptyDomain) {
        TRACE(' - restarting op from same pc...');
        if (!wasMetaOp) restartedRelevantOp = true; // TODO: undo this particular step if the restart results in the offset becoming a jmp?

        --constraints; // Constraint may have been eliminated
      }
    }

    if (emptyDomain) {
      return ops;
    }

    return THROW('Derailed; expected to find STOP before EOF');
  }

  function min_moveTo(ml, offset, len) {
    TRACE(' - trying to move from', offset, 'to', offset + len, 'delta = ', len);

    switch (ml_dec8(ml, offset + len)) {
      case ML_NOOP:
      case ML_NOOP2:
      case ML_NOOP3:
      case ML_NOOP4:
      case ML_JMP:
      case ML_JMP32:
        TRACE('- moving to another jump so merging them now');
        ml_compileJumpAndConsolidate(ml, offset, len);
        pc = offset; // Restart, make sure the merge worked

        break;

      default:
        pc = offset + len;
        break;
    }
  }

  function min_same(ml, offset) {
    // Loop through the args and alias each one to the previous. then eliminate the constraint. it is an artifact.
    var argCount = ml_dec16(ml, offset + 1);
    TRACE(' = min_same', argCount, 'x');

    if (argCount === 2) {
      if (readIndex(ml, offset + OFFSET_C_A) === readIndex(ml, offset + OFFSET_C_B)) {
        TRACE(' - argcount=2 and A==B so eliminating constraint');
        ml_eliminate(ml, offset, SIZEOF_C_2);
        return;
      }
    }

    if (argCount > 1) {
      TRACE(' - aliasing all args to the first arg, intersecting all domains, and eliminating constraint');
      var firstIndex = readIndex(ml, offset + SIZEOF_C);
      var F = getDomain(firstIndex, true);
      TRACE(' - indexF=', firstIndex, ', F=', domain__debug(F));

      for (var i = 1; i < argCount; ++i) {
        var indexD = readIndex(ml, offset + SIZEOF_C + i * 2);

        if (indexD !== firstIndex) {
          var D = getDomain(indexD, true);
          TRACE('   - pos:', i, ', aliasing index', indexD, 'to F, intersecting', domain__debug(D), 'with', domain__debug(F), 'to', domain__debug(domain_intersection(F, D)));
          F = intersectAndAlias(indexD, firstIndex, D, F);

          if (!F) {
            TRACE('   !! Caused an empty domain. Failing.');
            break;
          }
        }
      }
    }

    TRACE(' - eliminating same() constraint');
    ml_eliminate(ml, offset, SIZEOF_C + argCount * 2);
  }

  function min_diff_2(ml, offset) {
    TRACE(' - min_diff_2');
    ASSERT(ml_dec16(ml, offset + 1) === 2, 'should be arg count = 2');
    var offsetA = offset + OFFSET_C_A;
    var offsetB = offset + OFFSET_C_B;
    var indexA = readIndex(ml, offsetA);
    var indexB = readIndex(ml, offsetB);
    var A = getDomainFast(indexA);
    var B = getDomainFast(indexB);
    TRACE(' -', indexA, '!=', indexB, '   ->   ', domain__debug(A), '!=', domain__debug(B));
    if (!A || !B) return true;

    if (indexA === indexB) {
      TRACE(' - A != A, falsum, artifact case');
      setEmpty(indexA, 'X!=X falsum');
      return true;
    }

    var solved = false; // If either is solved then the other domain should
    // become the result of unsolved_set "minus" solved_set

    var vA = domain_getValue(A);

    if (vA >= 0) {
      var oB = B;
      B = domain_removeValue(B, vA);
      if (oB !== B && updateDomain(indexB, B, 'A != B with A solved')) return true;
      solved = true;
    } else {
      var vB = domain_getValue(B);

      if (domain_getValue(B) >= 0) {
        var oA = A;
        A = domain_removeValue(A, vB);
        if (A !== oA && updateDomain(indexA, A, 'A != B with B solved')) return true;
        solved = true;
      }
    } // If the two domains share no elements the constraint is already satisfied


    if (!solved && !domain_intersection(A, B)) solved = true;
    TRACE(' ->', domain__debug(A), '!=', domain__debug(B), ', solved?', solved); // Solved if the two domains (now) intersect to an empty domain

    if (solved) {
      TRACE(' - No element overlapping between', indexA, 'and', indexB, 'left so we can eliminate this diff');
      ASSERT(domain_sharesNoElements(A, B), 'if A or B solves, the code should have solved the diff');
      ml_eliminate(ml, offset, SIZEOF_C_2);
      return true;
    }

    TRACE(' - min_diff_2 changed nothing');
    return false;
  }

  function min_lt(ml, offset) {
    var offsetA = offset + OFFSET_C_A;
    var offsetB = offset + OFFSET_C_B;
    var indexA = readIndex(ml, offsetA);
    var indexB = readIndex(ml, offsetB);
    var A = getDomainFast(indexA);
    var B = getDomainFast(indexB);
    TRACE(' = min_lt', indexA, '<', indexB, '   ->   ', domain__debug(A), '<', domain__debug(B));
    if (indexA === indexB) return setEmpty(indexA, 'X<X falsum'); // (relevant) artifact case

    if (!A || !B) return; // Relative comparison is easy; cut away any non-intersecting
    // values that violate the desired outcome. only when a A and
    // B have multiple intersecting values we have to keep this
    // constraint

    var oA = A;
    A = domain_removeGte(A, domain_max(B));

    if (A !== oA) {
      TRACE(' - updating A to', domain__debug(A));
      if (updateDomain(indexA, A, 'A lt B')) return;
    }

    var oB = B;
    B = domain_removeLte(B, domain_min(A));

    if (B !== oB) {
      TRACE(' - updating B to', domain__debug(B));
      if (updateDomain(indexB, B, 'A lt B')) return;
    } // Any value in A must be < any value in B


    if (domain_max(A) < domain_min(B)) {
      TRACE(' - Eliminating lt because max(A)<min(B)');
      ml_eliminate(ml, offset, SIZEOF_C_2);
    } else {
      TRACE(' - not only jumps...');
      onlyJumps = false;
      pc = offset + SIZEOF_C_2;
    }
  }

  function min_lte(ml, offset) {
    var offsetA = offset + OFFSET_C_A;
    var offsetB = offset + OFFSET_C_B;
    var indexA = readIndex(ml, offsetA);
    var indexB = readIndex(ml, offsetB);
    var A = getDomainFast(indexA);
    var B = getDomainFast(indexB);
    TRACE(' = min_lte', indexA, '<=', indexB, '   ->   ', domain__debug(A), '<=', domain__debug(B));
    if (!A || !B) return;

    if (indexA === indexB) {
      TRACE(' - Eliminating lte because max(A)<=min(A) is a tautology (once solved)');
      ml_eliminate(ml, offset, SIZEOF_C_2);
      return;
    } // Relative comparison is easy; cut away any non-intersecting
    // values that violate the desired outcome. only when a A and
    // B have multiple intersecting values we have to keep this
    // constraint


    TRACE(' - index A!=B so remove all >max(B) from A', domain__debug(A), domain_max(B), '->', domain__debug(domain_removeGtUnsafe(A, domain_max(B))));
    var oA = A;
    A = domain_removeGtUnsafe(A, domain_max(B));

    if (A !== oA) {
      TRACE(' - Updating A to', domain__debug(A));
      if (updateDomain(indexA, A, 'A lte B')) return;
    } // A is (now) empty so just remove it


    var oB = B;
    B = domain_removeLtUnsafe(B, domain_min(A));

    if (B !== oB) {
      TRACE(' - Updating B to', domain__debug(B));
      if (updateDomain(indexB, B, 'A lte B')) return;
    }

    TRACE(' ->', domain__debug(A), '<=', domain__debug(B), ', bp?', domain_isBoolyPair(A), '<=', domain_isBoolyPair(B), ', max:', domain_max(A), '<=', domain_max(B)); // Any value in A must be < any value in B

    if (domain_max(A) <= domain_min(B)) {
      TRACE(' - Eliminating lte because max(A)<=min(B)');
      ml_eliminate(ml, offset, SIZEOF_C_2);
    } else if (domain_isBoolyPair(A) && domain_isBoolyPair(B) && domain_max(A) <= domain_max(B)) {
      TRACE(' - A and B boolypair with max(A)<=max(B) so this is implication');
      TRACE_MORPH('A <= B', 'B -> A');
      ml_c2c2(ml, offset, 2, ML_IMP, indexA, indexB); // Have to add a solvestack entry to prevent a solution [01]->1 which would satisfy IMP but not LTE

      solveStack.push(function (_, force, getDomain, setDomain) {
        TRACE(' - min_lte; enforcing LTE', indexA, '<=', indexB, ' => ', domain__debug(getDomain(indexA)), '<=', domain__debug(getDomain(indexB)));
        var A = getDomain(indexA);
        var B = getDomain(indexB);

        if (domain_hasNoZero(A)) {
          B = domain_removeValue(B, 0);
          setDomain(indexB, B);
        } else if (domain_isZero(B) || domain_isBooly(A)) {
          A = domain_removeGtUnsafe(A, 0);
          setDomain(indexA, A);
        }

        ASSERT(getDomain(indexA));
        ASSERT(getDomain(indexB));
        ASSERT(domain_max(getDomain(indexA)) <= domain_min(getDomain(indexB)), 'must hold lte', domain__debug(A), '<=', domain__debug(B));
      });
    } else {
      TRACE(' - not only jumps...');
      onlyJumps = false;
      pc = offset + SIZEOF_C_2;
    }
  }

  function min_nall(ml, offset) {
    var offsetCount = offset + 1;
    var argCount = ml_dec16(ml, offsetCount);
    var offsetArgs = offset + SIZEOF_C;
    var opSize = SIZEOF_C + argCount * 2;
    TRACE(' = min_nall', argCount, 'x');
    TRACE('  - ml for this nall:', ml.slice(offset, offset + opSize).join(' '));
    TRACE('  -', Array.from(Array(argCount)).map(function (n, i) {
      return readIndex(ml, offsetArgs + i * 2);
    }));
    TRACE('  -', Array.from(Array(argCount)).map(function (n, i) {
      return domain__debug(getDomainFast(readIndex(ml, offsetArgs + i * 2)));
    }));
    if (!argCount) return setEmpty(-1, 'nall without args is probably a bug');

    if (argCount === 2) {
      if (min_nall_2(ml, offset)) return;
    }

    var countStart = argCount;
    var lastIndex = -1;
    var lastDomain; // A nall only ensures at least one of its arg solves to zero

    for (var i = argCount - 1; i >= 0; --i) {
      // Backwards because we're pruning dud indexes
      var index = readIndex(ml, offsetArgs + i * 2);
      var domain = getDomainFast(index);
      TRACE('  - loop i=', i, 'index=', index, 'domain=', domain__debug(domain));
      if (!domain) return;

      if (domain_min(domain) > 0 || lastIndex === index) {
        // Remove var from list
        TRACE(lastIndex === index ? ' - removing redundant dupe var from nall' : ' - domain contains no zero so remove var from this constraint'); // Now
        // - move all indexes bigger than the current back one position
        // - compile the new count back in
        // - compile a NOOP in the place of the last element

        TRACE('  - moving further domains one space forward (from ', i + 1, ' / ', argCount, ')');
        min_spliceArgSlow(ml, offsetArgs, argCount, i, false);
        --argCount;
      } else if (domain_isZero(domain)) {
        // Remove constraint
        TRACE(' - domain solved to zero so constraint is satisfied');
        ml_eliminate(ml, offset, SIZEOF_C + 2 * countStart);
        return;
      } else {
        // Arg contains a 0 and is unsolved
        TRACE(' - domain contains zero and is not solved so leave it alone');
        lastIndex = index;
        lastDomain = domain;
      }
    }

    if (argCount === 0) {
      TRACE(' - Nall has no var left to be zero; rejecting problem'); // This is a bad state: all vars were removed from this constraint which
      // means none of the args were zero and the constraint doesnt hold

      return setEmpty(lastIndex, 'nall; none of the args were zero');
    }

    if (argCount === 1) {
      TRACE(' - Nall has one var left; forcing it to zero'); // Force set last index to zero and remove constraint. this should not
      // reject (because then the var would have been removed in loop above)
      // but do it "safe" anyways, just in case.

      var _domain = domain_removeGtUnsafe(lastDomain, 0);

      if (lastDomain !== _domain && updateDomain(lastIndex, _domain)) return;
      ml_eliminate(ml, offset, SIZEOF_C + 2 * countStart);
    } else if (countStart !== argCount) {
      TRACE(' - recording new argcount and freeing up space');
      ml_enc16(ml, offsetCount, argCount); // Write new count

      var free = (countStart - argCount) * 2;
      ml_compileJumpSafe(ml, offset + opSize - free, free); // Note: still have to restart op because ml_jump may have clobbered the old end of the op with a new jump
    } else {
      TRACE(' - not only jumps...');
      onlyJumps = false;
      pc = offset + opSize;
    }
  }

  function min_nall_2(ml, offset) {
    var offsetA = offset + OFFSET_C_A;
    var offsetB = offset + OFFSET_C_B;
    var indexA = readIndex(ml, offsetA);
    var indexB = readIndex(ml, offsetB);
    var A = getDomainFast(indexA);
    var B = getDomainFast(indexB);
    TRACE(' = min_nall_2', indexA, '!&', indexB, '   ->   ', domain__debug(A), '!&', domain__debug(B));
    ASSERT(ml_dec16(ml, offset + 1) === 2, 'nall should have 2 args');
    if (!A || !B) return true;

    if (indexA === indexB) {
      TRACE(' - indexA==indexB so A=0 and eliminate constraint');
      var oA = A;
      A = domain_removeGtUnsafe(A, 0);
      if (A !== oA) updateDomain(indexA, A, '`A !& A` means A must be zero');
      ml_eliminate(ml, offset, SIZEOF_C_2);
      return true;
    }

    if (domain_isZero(A) || domain_isZero(B)) {
      TRACE(' - A=0 or B=0, eliminating constraint');
      ml_eliminate(ml, offset, SIZEOF_C_2);
      return true;
    }

    if (domain_hasNoZero(A)) {
      TRACE(' - A>=1 so B must be 0');
      var oB = B;
      B = domain_removeGtUnsafe(B, 0);
      if (B !== oB) updateDomain(indexB, B, 'nall[2] B');
      ml_eliminate(ml, offset, SIZEOF_C_2);
      return true;
    }

    if (domain_hasNoZero(B)) {
      TRACE(' - B>=1 so A must be 0');
      var _oA = A;
      A = domain_removeGtUnsafe(A, 0);
      if (A !== _oA) updateDomain(indexA, A, 'nall[2] A');
      ml_eliminate(ml, offset, SIZEOF_C_2);
      return true;
    }

    TRACE(' - min_nall_2 changed nothing');
    return false;
  }

  function min_some(ml, offset) {
    var offsetCount = offset + 1;
    var argCount = ml_dec16(ml, offsetCount);
    var offsetArgs = offset + SIZEOF_C;
    var opSize = SIZEOF_C + argCount * 2;
    TRACE(' = min_some', argCount, 'x');
    TRACE('  - ml for this some:', ml.slice(offset, offset + opSize).join(' '));
    TRACE('  -', Array.from(Array(argCount)).map(function (n, i) {
      return readIndex(ml, offsetArgs + i * 2);
    }));
    TRACE('  -', Array.from(Array(argCount)).map(function (n, i) {
      return domain__debug(getDomainFast(readIndex(ml, offsetArgs + i * 2)));
    }));
    if (!argCount) return setEmpty(-1, 'some without args is probably a bug');

    if (argCount === 2) {
      if (min_some_2(ml, offset)) return;
    }

    var countStart = argCount;
    var lastIndex = -1;
    var lastDomain; // A some only ensures at least one of its arg solves to zero

    for (var i = argCount - 1; i >= 0; --i) {
      // Backwards because we're pruning dud indexes
      var index = readIndex(ml, offsetArgs + i * 2);
      var domain = getDomainFast(index);
      TRACE('  - loop i=', i, 'index=', index, 'domain=', domain__debug(domain));
      if (!domain) return;

      if (domain_isZero(domain) || lastIndex === index) {
        // Remove var from list
        TRACE(lastIndex === index ? ' - removing redundant dupe var from some' : ' - domain contains no zero so remove var from this constraint'); // Now
        // - move all indexes bigger than the current back one position
        // - compile the new count back in
        // - compile a NOOP in the place of the last element

        TRACE('  - moving further domains one space forward (from ', i + 1, ' / ', argCount, ')');
        min_spliceArgSlow(ml, offsetArgs, argCount, i, false);
        --argCount;
      } else if (domain_hasNoZero(domain)) {
        // Remove constraint
        TRACE(' - domain solved to nonzero so constraint is satisfied');
        ml_eliminate(ml, offset, SIZEOF_C + 2 * countStart);
        return;
      } else {
        // Arg contains a 0 and is unsolved
        TRACE(' - domain contains zero and is not solved so leave it alone');
        lastIndex = index;
        lastDomain = domain;
      }
    }

    if (argCount === 0) {
      TRACE(' - Some has no var left to be zero; rejecting problem'); // This is a bad state: all vars were removed from this constraint which
      // means all of the args were zero and the constraint doesnt hold

      return setEmpty(lastIndex, 'some; all of the args were zero');
    }

    if (argCount === 1) {
      TRACE(' - Some has one var left; forcing it to nonzero'); // Force set last index to nonzero and remove constraint. this should not
      // reject (because then the var would have been removed in loop above)
      // but do it "safe" anyways, just in case.

      var _domain2 = domain_removeValue(lastDomain, 0);

      if (lastDomain !== _domain2 && updateDomain(lastIndex, _domain2)) return;
      ml_eliminate(ml, offset, SIZEOF_C + 2 * countStart);
    } else if (countStart !== argCount) {
      TRACE(' - recording new argcount and freeing up space');
      ml_enc16(ml, offsetCount, argCount); // Write new count

      var free = (countStart - argCount) * 2;
      ml_compileJumpSafe(ml, offset + opSize - free, free); // Note: still have to restart op because ml_jump may have clobbered the old end of the op with a new jump
    } else {
      TRACE(' - not only jumps...');
      onlyJumps = false;
      pc = offset + opSize;
    }
  }

  function min_isAll(ml, offset) {
    var offsetCount = offset + 1;
    var argCount = ml_dec16(ml, offsetCount);
    var opSize = SIZEOF_C + 2 + argCount * 2;
    var offsetArgs = offset + SIZEOF_C;
    var offsetR = offset + opSize - 2;
    var indexR = readIndex(ml, offsetR);
    var R = getDomainFast(indexR);
    TRACE(' = min_isAll', argCount, 'x');
    TRACE('  - ml for this isAll (' + opSize + 'b):', ml.slice(offset, offset + opSize).join(' '));
    TRACE('  -', indexR, '= all?(', [].concat(Array(argCount)).map(function (n, i) {
      return readIndex(ml, offsetArgs + i * 2);
    }), ')');
    TRACE('  -', domain__debug(R), '= all?(', [].concat(Array(argCount)).map(function (n, i) {
      return domain__debug(getDomainFast(readIndex(ml, offsetArgs + i * 2)));
    }), ')');
    if (!R) return;

    if (domain_isZero(R)) {
      TRACE(' - R is 0 so morph to nall and revisit'); // Compile to nall and revisit

      ml_enc8(ml, offset, ML_NALL);
      ml_compileJumpSafe(ml, offset + opSize - 2, 2); // Difference between nall with R=0 and an isAll is the result var (16bit)

      return;
    }

    if (domain_hasNoZero(R)) {
      TRACE(' - R is non-zero so remove zero from all args and eliminate constraint');

      for (var i = 0; i < argCount; ++i) {
        var index = readIndex(ml, offsetArgs + i * 2);
        var domain = getDomainFast(index);
        TRACE('    - index=', index, 'dom=', domain__debug(domain));
        if (!domain) return;
        var newDomain = domain_removeValue(domain, 0);
        if (newDomain !== domain && updateDomain(index, newDomain)) return;
      }

      ml_eliminate(ml, offset, opSize);
      return;
    } // R is unresolved. check whether R can be determined


    ASSERT(domain_min(R) === 0 && domain_max(R) > 0, 'R is unresolved here', R);
    var allNonZero = true;
    var someAreZero = false;
    var someNonZero = false;

    for (var _i = 0; _i < argCount; ++_i) {
      var _index = readIndex(ml, offsetArgs + _i * 2);

      var _domain3 = getDomainFast(_index);

      TRACE('    - index=', _index, 'dom=', domain__debug(_domain3)); // Reflect isAll,
      // R=0 when at least one arg is zero
      // R>0 when all args have no zero

      if (domain_isZero(_domain3)) {
        TRACE(' - found a zero, breaking loop because R=0');
        someAreZero = true;
        break; // This permanently sets R to 0; no need to loop further
      } else if (domain_min(_domain3) === 0) {
        // Arg has zero and non-zero values so R (at least) cant be set to 1 yet
        allNonZero = false;
      } else {
        someNonZero = true;
      }
    }

    if (someAreZero) {
      TRACE(' - At least one arg was zero so R=0 and constraint can be removed');
      var oR = R;
      R = domain_removeGtUnsafe(R, 0);
      if (R !== oR) updateDomain(indexR, R);
      ml_eliminate(ml, offset, opSize);
      return;
    }

    if (allNonZero) {
      TRACE(' - No arg had zero so R=1 and constraint can be removed');
      var _oR = R;
      R = domain_removeValue(R, 0);
      if (R !== _oR) updateDomain(indexR, R);
      ml_eliminate(ml, offset, opSize);
      return;
    } // Remove all non-zero values from the list. this reduces their connection count and simplifies this isall


    if (someNonZero) {
      var removed = 0;

      for (var _i2 = argCount - 1; _i2 >= 0; --_i2) {
        var _index2 = readIndex(ml, offsetArgs + _i2 * 2);

        var _domain4 = getDomainFast(_index2);

        TRACE('   - checking if index', _index2, '(domain', domain__debug(_domain4), ') contains no zero so we can remove it from this isall');

        if (domain_hasNoZero(_domain4)) {
          // Now
          // - move all indexes bigger than the current back one position
          // - compile the new count back in
          // - compile a NOOP in the place of the last element
          TRACE('  - moving further domains one space forward (from ', _i2 + 1, ' / ', argCount, ')');
          min_spliceArgSlow(ml, offsetArgs, argCount, _i2, true);
          --argCount;
          ++removed;
        }
      }

      ml_enc16(ml, offset + 1, argCount); // Now "blank out" the space of eliminated constants, they should be at the end of the op

      var newOpSize = opSize - removed * 2;
      ml_compileJumpSafe(ml, offset + newOpSize, opSize - newOpSize);
      TRACE(' - Removed', removed, 'non-zero args from unsolved isall, has', argCount, 'left');
      TRACE(' - ml for this sum now:', ml.slice(offset, offset + opSize).join(' '));
      if (argCount === 1) _min_isAllMorphToXnor(ml, offset, argCount, offsetArgs, indexR);
      return;
    }

    if (argCount === 1) return _min_isAllMorphToXnor(ml, offset, argCount, offsetArgs, indexR);
    TRACE(' - not only jumps...');
    onlyJumps = false;
    pc = offset + opSize;
  }

  function _min_isAllMorphToXnor(ml, offset, argCount, offsetArgs, indexR) {
    // While this usually only happens when eliminating non-zeroes, there may be an artifact where a script
    // generated an isall with just one arg. kind of silly but whatever, right.
    TRACE(' - Only one arg remaining; morphing to a XNOR');
    ASSERT(argCount > 0, 'isall must have at least one arg in order to have enough space for the xnor morph');
    var index = readIndex(ml, offsetArgs);
    ml_cr2c2(ml, offset, argCount, ML_XNOR, indexR, index);
    varChanged = true; // The xnor may need optimization
  }

  function min_isNall(ml, offset) {
    var offsetCount = offset + 1;
    var argCount = ml_dec16(ml, offsetCount);
    var opSize = SIZEOF_C + argCount * 2 + 2;
    var offsetArgs = offset + SIZEOF_C;
    var offsetR = offset + opSize - 2;
    var indexR = readIndex(ml, offsetR);
    var R = getDomainFast(indexR);
    TRACE(' = min_isNall', argCount, 'x');
    TRACE('  - ml for this isNall:', ml.slice(offset, offset + opSize).join(' '));
    TRACE('  -', indexR, '= nall?(', [].concat(Array(argCount)).map(function (n, i) {
      return readIndex(ml, offsetArgs + i * 2);
    }), ')');
    TRACE('  -', domain__debug(R), '= nall?(', [].concat(Array(argCount)).map(function (n, i) {
      return domain__debug(getDomainFast(readIndex(ml, offsetArgs + i * 2)));
    }), ')');
    if (!R) return;

    if (domain_isZero(R)) {
      TRACE(' - R=0 so; !nall so; all so; we must remove zero from all args and eliminate constraint');

      for (var i = 0; i < argCount; ++i) {
        var index = readIndex(ml, offsetArgs + i * 2);
        var domain = getDomainFast(index);
        TRACE('    - index=', index, 'dom=', domain__debug(domain));
        if (!domain) return;
        var newDomain = domain_removeValue(domain, 0);
        if (newDomain !== domain && updateDomain(index, newDomain)) return;
      }

      ml_eliminate(ml, offset, opSize);
      return;
    }

    if (domain_hasNoZero(R)) {
      TRACE(' - R>0 so; nall. just morph and revisit');
      ml_enc8(ml, offset, ML_NALL);
      ml_compileJumpSafe(ml, offset + opSize - 2, 2); // Difference between nall and isNall is the result var (16bit)

      return;
    } // R is unresolved. check whether R can be determined


    ASSERT(domain_min(R) === 0 && domain_max(R) > 0, 'R is unresolved here', R);
    var allNonZero = true;
    var someAreZero = false;

    for (var _i3 = 0; _i3 < argCount; ++_i3) {
      var _index3 = readIndex(ml, offsetArgs + _i3 * 2);

      var _domain5 = getDomainFast(_index3);

      TRACE('    - index=', _index3, 'dom=', domain__debug(_domain5)); // Reflect isNall,
      // R=0 when all args have no zero
      // R>0 when at least one arg is zero

      if (domain_isZero(_domain5)) {
        TRACE(' - found a zero, breaking loop because R=0');
        someAreZero = true;
        break; // This permanently sets R to 0; no need to loop further
      } else if (domain_min(_domain5) === 0) {
        // Arg has zero and non-zero values so R (at least) cant be set to 1 yet
        allNonZero = false;
      }
    }

    if (someAreZero) {
      TRACE(' - At least one arg was zero so R>=1 and constraint can be removed');
      var oR = R;
      R = domain_removeValue(R, 0);
      if (R !== oR) updateDomain(indexR, R, 'isnall, R>=1 because at least one var was zero');
      ml_eliminate(ml, offset, opSize);
    } else if (allNonZero) {
      TRACE(' - No arg had a zero so R=0 and constraint can be removed');
      var _oR2 = R;
      R = domain_removeGtUnsafe(R, 0);
      if (R !== _oR2) updateDomain(indexR, R);
      ml_eliminate(ml, offset, opSize);
    } else {
      // TODO: prune all args here that are nonzero? is that worth it?
      TRACE(' - not only jumps...');
      onlyJumps = false;
      pc = offset + opSize;
    }
  }

  function min_isSome(ml, offset) {
    var offsetCount = offset + 1;
    var argCount = ml_dec16(ml, offsetCount);
    var opSize = SIZEOF_C + argCount * 2 + 2;
    var offsetArgs = offset + SIZEOF_C;
    var offsetR = offset + opSize - 2;
    var indexR = readIndex(ml, offsetR);
    var R = getDomainFast(indexR);
    TRACE(' = min_isSome', argCount, 'x');
    TRACE('  - ml for this isSome:', ml.slice(offset, offset + opSize).join(' '));
    TRACE('  -', indexR, '= some?(', [].concat(Array(argCount)).map(function (n, i) {
      return readIndex(ml, offsetArgs + i * 2);
    }), ')');
    TRACE('  -', domain__debug(R), '= some?(', [].concat(Array(argCount)).map(function (n, i) {
      return domain__debug(getDomainFast(readIndex(ml, offsetArgs + i * 2)));
    }), ')');
    if (!R) return;

    if (domain_isZero(R)) {
      TRACE(' - R=0 so; !some so; none so; we must force zero to all args and eliminate constraint');

      for (var i = 0; i < argCount; ++i) {
        var index = readIndex(ml, offsetArgs + i * 2);
        var domain = getDomainFast(index);
        TRACE('    - index=', index, 'dom=', domain__debug(domain));
        if (!domain) return;
        var newDomain = domain_removeGtUnsafe(domain, 0);
        if (newDomain !== domain && updateDomain(index, newDomain)) return;
      }

      ml_eliminate(ml, offset, opSize);
      return;
    }

    if (domain_hasNoZero(R)) {
      TRACE(' - R>0 so; some. just morph and revisit');
      ml_enc8(ml, offset, ML_SOME);
      ml_compileJumpSafe(ml, offset + opSize - 2, 2); // Difference between some and isSome is the result var (16bit)

      return;
    } // R is unresolved. check whether R can be determined


    ASSERT(domain_min(R) === 0 && domain_max(R) > 0, 'R is unresolved here', R);
    var someNonZero = false;
    var allZero = true;
    var someZero = false;

    for (var _i4 = 0; _i4 < argCount; ++_i4) {
      var _index4 = readIndex(ml, offsetArgs + _i4 * 2);

      var _domain6 = getDomainFast(_index4);

      TRACE('    - index=', _index4, 'dom=', domain__debug(_domain6)); // Reflect isSome,
      // R=0 when all args are zero (already checked above)
      // R>0 when at least one arg is nonzero

      if (domain_hasNoZero(_domain6)) {
        TRACE(' - found a nonzero, breaking loop because R>0');
        someNonZero = true;
        break; // This permanently sets R to 0; no need to loop further
      } else if (domain_isZero(_domain6)) {
        someZero = true;
      } else {
        allZero = false;
      }
    }

    if (someNonZero) {
      TRACE(' - At least one arg was zero so R>=1 and constraint can be removed');
      var oR = R;
      R = domain_removeValue(R, 0);
      if (R !== oR) updateDomain(indexR, R, 'issome, R>=1 because at least one var was nonzero');
      ml_eliminate(ml, offset, opSize);
    } else if (allZero) {
      TRACE(' - All vars were zero so R=0 and constraint can be removed');
      var _oR3 = R;
      R = domain_removeGtUnsafe(R, 0);
      if (R !== _oR3) updateDomain(indexR, R, 'issome, R>=1 because all vars were zero');
      ml_eliminate(ml, offset, opSize);
    } else if (someZero) {
      TRACE(' - Some vars were zero, removing them from the args'); // Force constants to the end

      ml_heapSort16bitInline(ml, pc + SIZEOF_C, argCount); // We know
      // - these args do not contain non-zero args
      // - all constants are moved to the back
      // - there is at least one constant 0
      // - not all args were 0
      // so we can move back the result var

      var argOffset = offsetArgs + argCount * 2 - 2;
      TRACE(' - offset:', offset, ', argCount:', argCount, ', args offset:', offsetArgs, ', first arg domain:', domain__debug(getDomain(readIndex(ml, offsetArgs))), ', last arg offset:', argOffset, ', last domain:', domain__debug(getDomain(readIndex(ml, argOffset))));
      TRACE(' - op before:', ml__debug(ml, offset, 1, problem));
      ASSERT(domain_isZero(getDomain(readIndex(ml, argOffset))), 'at least the last arg should be zero', domain__debug(getDomain(readIndex(ml, argOffset))));
      ASSERT(!domain_isZero(getDomain(readIndex(ml, offsetArgs))), 'the first arg should not be zero', domain__debug(getDomain(readIndex(ml, offsetArgs)))); // Search for the first non-zero arg

      var newArgCount = argCount;

      while (domain_isZero(getDomain(readIndex(ml, argOffset)))) {
        argOffset -= 2;
        --newArgCount;
      }

      TRACE(' - last non-zero arg is arg number', newArgCount, 'at', argOffset, ', index:', readIndex(ml, argOffset), ', domain:', domain__debug(getDomain(readIndex(ml, argOffset))));

      if (newArgCount === 1) {
        TRACE(' - there is one arg left, morph to XNOR');
        TRACE_MORPH('R = some?(A 0 0 ..)', 'R !^ A');
        var indexA = readIndex(ml, offsetArgs);
        ml_cr2c2(ml, offset, argCount, ML_XNOR, indexR, indexA);
      } else {
        TRACE(' - moving R to the first zero arg at offset', argOffset + 2, 'and compiling a jump for the rest'); // Copy the result var over the first zero arg

        ml_enc16(ml, offset + 1, newArgCount);
        ml_enc16(ml, argOffset + 2, indexR);
        ml_compileJumpSafe(ml, argOffset + 4, (argCount - newArgCount) * 2);
        ASSERT(ml_validateSkeleton(ml, 'min_isSome; pruning zeroes'));
      }

      TRACE(' - op after:', ml__debug(ml, offset, 1, problem));
    } else {
      // TODO: prune all args here that are zero? is that worth it?
      TRACE(' - not only jumps...');
      onlyJumps = false;
      pc = offset + opSize;
    }
  }

  function min_isNone(ml, offset) {
    var offsetCount = offset + 1;
    var argCount = ml_dec16(ml, offsetCount);
    var opSize = SIZEOF_C + argCount * 2 + 2;
    var offsetArgs = offset + SIZEOF_C;
    var offsetR = offset + opSize - 2;
    var indexR = readIndex(ml, offsetR);
    var R = getDomainFast(indexR);
    TRACE(' = min_isNone', argCount, 'x');
    TRACE('  - ml for this isNone:', ml.slice(offset, offset + opSize).join(' '));
    TRACE('  -', indexR, '= none?(', [].concat(Array(argCount)).map(function (n, i) {
      return readIndex(ml, offsetArgs + i * 2);
    }), ')');
    TRACE('  -', domain__debug(R), '= none?(', [].concat(Array(argCount)).map(function (n, i) {
      return domain__debug(getDomainFast(readIndex(ml, offsetArgs + i * 2)));
    }), ')');
    if (!R) return;

    if (domain_hasNoZero(R)) {
      TRACE('    - R>=1 so set all args to zero and eliminate');

      for (var i = 0; i < argCount; ++i) {
        var index = readIndex(ml, offsetArgs + i * 2);
        var domain = getDomainFast(index);
        TRACE('    - index=', index, 'dom=', domain__debug(domain));
        if (!domain) return;
        var newDomain = domain_removeGtUnsafe(domain, 0);
        if (newDomain !== domain && updateDomain(index, newDomain)) return;
      }

      ml_eliminate(ml, offset, opSize);
      return;
    }

    if (domain_isZero(R)) {
      TRACE(' - R=0 so this is a SOME. just morph and revisit');
      TRACE_MORPH('0 = none?(A B C ...)', 'some(A B C ...)');
      ml_enc8(ml, offset, ML_SOME);
      ml_compileJumpSafe(ml, offset + opSize - 2, 2); // Difference between some and isNone is the result var (16bit)

      return;
    } // R has a zero or is zero, determine whether there is any nonzero arg, or whether they are all zero


    var nonZero = false;
    var allZero = true;

    for (var _i5 = 0; _i5 < argCount; ++_i5) {
      var _index5 = readIndex(ml, offsetArgs + _i5 * 2);

      var _domain7 = getDomainFast(_index5);

      TRACE('    - index=', _index5, 'dom=', domain__debug(_domain7)); // Reflect isNone,
      // R=0 when at least one arg is nonzero
      // R>0 when all args are zero

      if (domain_hasNoZero(_domain7)) {
        nonZero = true;
        break;
      }

      if (!domain_isZero(_domain7)) {
        allZero = false;
      }
    }

    if (nonZero) {
      TRACE(' - at least one arg had no zero so R=0, eliminate constraint');
      var oR = R;
      R = domain_removeGtUnsafe(R, 0);
      if (R !== oR) updateDomain(indexR, R, 'isnone R=0 because an arg had no zero');
      ml_eliminate(ml, offset, opSize);
    } else if (allZero) {
      TRACE(' - isnone, all args are 0 so R>=1, remove constraint');
      var _oR4 = R;
      R = domain_removeValue(R, 0);
      if (R !== _oR4) updateDomain(indexR, R, 'isnone R>=1 because all args were zero');
      ml_eliminate(ml, offset, opSize);
    } else {
      // TODO: prune all args here that are zero? is that worth it?
      TRACE(' - not only jumps...');
      onlyJumps = false;
      pc = offset + SIZEOF_C + argCount * 2 + 2;
    }
  }

  function min_diff(ml, offset) {
    var argCount = ml_dec16(ml, offset + 1);
    var offsetArgs = offset + SIZEOF_C;
    var opSize = SIZEOF_C + argCount * 2;
    TRACE(' = min_diff', argCount, 'x');
    TRACE('  - ml for this diff:', ml.slice(offset, offset + opSize).join(' '));
    TRACE('  - indexes:', [].concat(Array(argCount)).map(function (n, i) {
      return readIndex(ml, offsetArgs + i * 2);
    }).join(', '));
    TRACE('  - domains:', [].concat(Array(argCount)).map(function (n, i) {
      return domain__debug(getDomainFast(readIndex(ml, offsetArgs + i * 2)));
    }).join(', '));
    ASSERT(argCount, 'should have at least one arg or be eliminated');
    if (!argCount) return setEmpty(-1, 'diff without args is probably a bug');
    var countStart = argCount; // A diff is basically a pyramid of neq's; one for each unique pair of the set
    // we loop back to front because we're splicing out vars while looping

    for (var i = argCount - 1; i >= 0; --i) {
      var indexA = readIndex(ml, offsetArgs + i * 2);
      var A = getDomainFast(indexA);
      TRACE('  - loop i=', i, 'index=', indexA, 'domain=', domain__debug(A));
      if (!A) return;
      var v = domain_getValue(A);

      if (v >= 0) {
        TRACE('   - solved, so removing', v, 'from all other domains and index', indexA, 'from the constraint');

        for (var j = 0; j < argCount; ++j) {
          // Gotta loop through all args. args wont be removed in this loop.
          if (j !== i) {
            var indexB = readIndex(ml, offsetArgs + j * 2);
            var oB = getDomainFast(indexB);
            TRACE('    - loop j=', j, 'index=', indexB, 'domain=', domain__debug(oB));
            if (indexA === indexB) return updateDomain(indexA, domain_createEmpty(), 'diff had this var twice, x!=x is a falsum'); // Edge case

            var B = domain_removeValue(oB, v);
            if (B !== oB && updateDomain(indexB, B, 'diff arg')) return;
          }
        } // So none of the other args have v and none of them ended up empty
        // now
        // - move all indexes bigger than the current back one position
        // - compile the new count back in
        // - compile a NOOP in the place of the last element


        TRACE('  - moving further domains one space forward (from ', i + 1, ' / ', argCount, ')', i + 1 < argCount);
        min_spliceArgSlow(ml, offsetArgs, argCount, i, true); // Move R as well

        --argCount;
      }
    }

    if (argCount <= 1) {
      TRACE(' - Count is', argCount, '; eliminating constraint');
      ASSERT(argCount >= 0, 'cant be negative');
      ml_eliminate(ml, offset, opSize);
    } else if (argCount !== countStart) {
      TRACE('  - recompiling new count (', argCount, ')');
      ml_enc16(ml, offset + 1, argCount);
      TRACE('  - compiling noop into empty spots'); // This hasnt happened yet

      ml_compileJumpSafe(ml, offsetArgs + argCount * 2, (countStart - argCount) * 2); // Need to restart op because the skip may have clobbered the next op offset
    } else if (argCount === 2 && min_diff_2(ml, offset)) ; else {
      TRACE(' - not only jumps...', opSize);
      onlyJumps = false;
      pc = offset + opSize;
    }
  }

  function min_sum_2(ml, sumOffset) {
    var offsetA = sumOffset + OFFSET_C_A;
    var offsetB = sumOffset + OFFSET_C_B;
    var offsetR = sumOffset + OFFSET_C_R;
    var indexA = readIndex(ml, offsetA);
    var indexB = readIndex(ml, offsetB);
    var indexR = readIndex(ml, offsetR);
    var A = getDomainFast(indexA);
    var B = getDomainFast(indexB);
    var R = getDomainFast(indexR);
    TRACE(' = min_sum_2', indexR, '=', indexA, '+', indexB, '   ->   ', domain__debug(R), '=', domain__debug(A), '+', domain__debug(B));
    if (!A || !B || !R) return false;
    ASSERT(ml_dec8(ml, sumOffset) === ML_SUM, 'should be a sum with 2 args');
    ASSERT(ml_dec16(ml, sumOffset + 1) === 2, 'should have 2 args'); // Note: A + B = C   ==>   <loA + loB, hiA + hiB>
    // but:  A - B = C   ==>   <loA - hiB, hiA - loB>   (so the lo/hi of B gets swapped!)
    // keep in mind that any number oob <sub,sup> gets pruned in either case, this makes
    // plus and minus are not perfect (counter-intuitively): `[0, 2] - [0, 4] = [0, 2]`

    var ooA = A;
    var ooB = B;
    var ooR = R;
    var oA;
    var oB;
    var oR;
    var loops = 0;

    do {
      ++loops;
      TRACE(' - plus propagation step...', loops, domain__debug(R), '=', domain__debug(A), '+', domain__debug(B));
      oA = A;
      oB = B;
      oR = R;
      R = domain_intersection(R, domain_plus(A, B));
      A = domain_intersection(A, domain_minus(R, B));
      B = domain_intersection(B, domain_minus(R, A));
    } while (A !== oA || B !== oB || R !== oR);

    TRACE(' ->', 'R:', domain__debug(R), '= A:', domain__debug(A), '+ B:', domain__debug(B));

    if (loops > 1) {
      if (A !== ooA) updateDomain(indexA, A, 'plus A');
      if (B !== ooB) updateDomain(indexB, B, 'plus B');
      if (R !== ooR) updateDomain(indexR, R, 'plus R');
      if (!A || !B || !R) return false;
    }

    var vA = domain_getValue(A);
    var vB = domain_getValue(B);
    var vR = domain_getValue(R);
    ASSERT((vA >= 0) + (vB >= 0) + (vR >= 0) !== 2, 'if two vars are solved the third should be solved as well');

    if (vA >= 0 && vB >= 0) {
      // So vR>=0 as well
      TRACE(' - All args are solved so removing constraint');
      ASSERT(vR >= 0, 'if two are solved then all three must be solved');
      ml_eliminate(ml, sumOffset, SIZEOF_CR_2);
      return true;
    }

    if (vA >= 0) {
      ASSERT(vB < 0 && vR < 0);

      if (min_plusWithSolvedArg(sumOffset, indexB, indexA, indexR, A, B, R, vA, 'A', 'B')) {
        return true;
      }
    }

    if (vB >= 0) {
      ASSERT(vA < 0 && vR < 0);

      if (min_plusWithSolvedArg(sumOffset, indexA, indexB, indexR, B, A, R, vB, 'B', 'A')) {
        return true;
      }
    } //
    // TRACE(' - not only jumps');
    // onlyJumps = false;
    // pc = sumOffset + SIZEOF_CR_2;


    return false;
  }

  function intersectAndAlias(indexFrom, indexTo, F, T) {
    TRACE(' - intersectAndAlias; from index:', indexFrom, ', to index:', indexTo, ', F:', domain__debug(F), ', T:', domain__debug(T), ', FT:', domain__debug(domain_intersection(F, T)));
    ASSERT(typeof indexFrom === 'number' && indexFrom >= 0, 'indexfrom check');
    ASSERT(typeof indexTo === 'number' && indexTo >= 0, 'indexto check');
    ASSERT(F && T, 'should not receive empty domains... catch this at caller');
    ASSERT_NORDOM(F);
    ASSERT_NORDOM(T);
    ASSERT(getDomain(indexFrom) === F, 'F should match domain');
    ASSERT(getDomain(indexTo) === T, 'T should match domain');
    var FT = domain_intersection(F, T);

    if (F !== T) {
      updateDomain(indexTo, FT, 'intersectAndAlias');
    }

    if (FT && !domain_isSolved(F)) addAlias(indexFrom, indexTo);
    return FT;
  }

  function min_plusWithSolvedArg(sumOffset, indexY, indexX, indexR, X, Y, R, vX, nameX, nameY) {
    TRACE(' - min_plusWithSolvedArg', nameX, nameY, domain__debug(R), '=', domain__debug(X), '+', domain__debug(Y));
    ASSERT(vX >= 0, 'caller should assert that X is solved');
    ASSERT(domain_isSolved(Y) + domain_isSolved(R) === 0, 'caller should assert that only one of the three is solved');

    if (vX === 0) {
      TRACE(' -', nameX, '= 0, so R =', nameY, '+ 0, so R ==', nameY, ', morphing op to eq'); // Morph R=0+Y to R==Y

      intersectAndAlias(indexR, indexY, R, Y);
      ml_eliminate(ml, sumOffset, SIZEOF_CR_2);
      varChanged = true;
      return true;
    } // Try to morph R=x+Y to x=R==?Y when R has two values and Y is [0, 1] (because it cant be solved, so not 0 nor 1)
    // R    = A + B           ->        B    = A ==? R    (when B is [01] and A is solved)
    // [01] = 1 + [01]        ->        [01] = 1 !=? [0 1]
    // [12] = 1 + [01]        ->        [01] = 1 !=? [1 2]
    // [10 11] = 10 + [01]    ->        [01] = 10 !=? [10 11]
    // rationale; B=bool means the solved value in A can only be A or
    // A+1. when B=1 then R=A+1 and diff. when B=0 then R=A and eq.
    // this only works when vX==max(R) because its either +0 or +1


    if (domain_isBool(Y) && domain_size(R) === 2 && domain_min(R) === vX) {
      TRACE(' - R = X + Y   ->   Y = X ==? R    (Y is [01] and X is solved to', vX, ')');
      TRACE('   - R =', vX, '+', nameY, 'to', nameY, '=', vX, domain_max(R) === vX ? '==?' : '!=? R');
      TRACE('   -', domain__debug(R), '=', vX, '+', domain__debug(Y), 'to ', domain__debug(Y), '=', vX, '==?', domain__debug(R));
      TRACE(' - morphing R=A+B to B=A!=?R with A solved and B=[01] and size(R)=2');
      ml_cr2cr2(ml, sumOffset, 2, ML_ISDIFF, indexR, indexX, indexY);
      varChanged = true;
      return true;
    }

    TRACE('   - min_plusWithSolvedArg did nothing');
    return false;
  }

  function min_minus(ml, offset) {
    var offsetA = offset + 1;
    var offsetB = offset + 3;
    var offsetR = offset + 5;
    var indexA = readIndex(ml, offsetA);
    var indexB = readIndex(ml, offsetB);
    var indexR = readIndex(ml, offsetR);
    var A = getDomainFast(indexA);
    var B = getDomainFast(indexB);
    var R = getDomainFast(indexR);
    TRACE(' = min_minus', indexR, '=', indexA, '-', indexB, '   ->   ', domain__debug(R), '=', domain__debug(A), '-', domain__debug(B));
    if (!A || !B || !R) return; // C = A - B   -> A = B + C, B = C - A
    // note: A - B = C   ==>   <loA - hiB, hiA - loB>
    // but:  A + B = C   ==>   <loA + loB, hiA + hiB>   (so the lo/hi of B gets swapped!)
    // keep in mind that any number oob <sub,sup> gets trimmed in either case.
    // this trimming may affect "valid" numbers in the other domains so that needs back-propagation.

    var ooA = A;
    var ooB = B;
    var ooR = R;
    var oA;
    var oB;
    var oR;
    var loops = 0;

    do {
      ++loops;
      TRACE(' - minus propagation step...', loops, domain__debug(R), '=', domain__debug(A), '+', domain__debug(B));
      oA = A;
      oB = B;
      oR = R;
      R = domain_intersection(R, domain_minus(A, B));
      A = domain_intersection(A, domain_plus(R, B));
      B = domain_intersection(B, domain_minus(A, R));
    } while (A !== oA || B !== oB || R !== oR);

    TRACE(' ->', 'A:', domain__debug(A), 'B:', domain__debug(B), 'R:', domain__debug(R));

    if (loops > 1) {
      if (A !== ooA) updateDomain(indexA, A, 'minus A');
      if (B !== ooB) updateDomain(indexB, B, 'minus B');
      if (R !== ooR) updateDomain(indexR, R, 'minus R');
      if (!A || !B || !R) return;
    }

    ASSERT(domain_isSolved(A) + domain_isSolved(B) + domain_isSolved(R) !== 2, 'if two vars are solved the third should be solved as well');

    if (domain_isSolved(R) && domain_isSolved(A)) {
      // MinR==maxR&&minA==maxA
      ASSERT(domain_isSolved(B), 'if two are solved then all three must be solved');
      ml_eliminate(ml, offset, SIZEOF_VVV);
    } else if (domain_getValue(A) === 0) {
      // MaxA==0
      TRACE(' - A=0 so B==R, aliasing R to B, eliminating constraint');
      intersectAndAlias(indexR, indexB, R, B);
      ml_eliminate(ml, offset, SIZEOF_VVV);
      varChanged = true;
    } else if (domain_getValue(B) === 0) {
      // MaxB==0
      TRACE(' - B=0 so A==R, aliasing R to A, eliminating constraint');
      intersectAndAlias(indexR, indexA, R, A);
      ml_eliminate(ml, offset, SIZEOF_VVV);
      varChanged = true;
    } else {
      TRACE(' - not only jumps...');
      onlyJumps = false;
      pc = offset + SIZEOF_VVV;
    }
  }

  function min_product_2(ml, offset) {
    var offsetA = offset + OFFSET_C_A;
    var offsetB = offset + OFFSET_C_B;
    var offsetR = offset + OFFSET_C_R;
    var indexA = readIndex(ml, offsetA);
    var indexB = readIndex(ml, offsetB);
    var indexR = readIndex(ml, offsetR);
    var A = getDomainFast(indexA);
    var B = getDomainFast(indexB);
    var R = getDomainFast(indexR);
    TRACE(' = min_product_2', indexR, '=', indexA, '*', indexB, '   ->   ', domain__debug(R), '=', domain__debug(A), '*', domain__debug(B));

    if (!A || !B || !R) {
      TRACE(' - found empty domain, rejecting');
      return true;
    } // C = A * B, B = C / A, A = C / B
    // note: A * B = C   ==>   <loA * loB, hiA * hiB>
    // but:  A / B = C   ==>   <loA / hiB, hiA / loB> and has rounding/div-by-zero issues! instead use "inv-mul" tactic
    // keep in mind that any number oob <sub,sup> gets pruned in either case. x/0=0
    // when dividing "do the opposite" of integer multiplication. 5/4=[] because there is no int x st 4*x=5
    // only outer bounds are evaluated here...


    var ooA = A;
    var ooB = B;
    var ooR = R;
    var oA;
    var oB;
    var oR;
    var loops = 0;

    do {
      ++loops;
      TRACE(' - mul propagation step...', loops, domain__debug(R), '=', domain__debug(A), '*', domain__debug(B));
      oA = A;
      oB = B;
      oR = R;
      R = domain_intersection(R, domain_mul(A, B));
      A = domain_intersection(A, domain_invMul(R, B));
      B = domain_intersection(B, domain_invMul(R, A));
    } while (A !== oA || B !== oB || R !== oR);

    TRACE(' ->', 'A:', domain__debug(A), 'B:', domain__debug(B), 'R:', domain__debug(R));

    if (loops > 1) {
      if (A !== ooA) updateDomain(indexA, A, 'mul A');
      if (B !== ooB) updateDomain(indexB, B, 'mul B');
      if (R !== ooR) updateDomain(indexR, R, 'mul R');

      if (!A || !B || !R) {
        TRACE(' - found empty domain, rejecting');
        return true;
      }
    }

    ASSERT(domain_isSolved(A) + domain_isSolved(B) + domain_isSolved(R) !== 2 || domain_getValue(R) === 0, 'if two vars are solved the third should be solved as well unless R is 0');

    if (domain_isSolved(R) && domain_isSolved(A)) {
      TRACE(' - A B R all solved, eliminating constraint; ABR:', domain__debug(A), domain__debug(B), domain__debug(R));
      ASSERT(domain_isZero(R) || domain_isSolved(B), 'if two are solved then all three must be solved or R is zero');
      ml_eliminate(ml, offset, SIZEOF_CR_2);
      return true;
    }

    TRACE('   - min_product_2 did not do anything');
    return false;
  }

  function min_div(ml, offset) {
    var offsetA = offset + 1;
    var offsetB = offset + 3;
    var offsetR = offset + 5;
    var indexA = readIndex(ml, offsetA);
    var indexB = readIndex(ml, offsetB);
    var indexR = readIndex(ml, offsetR);
    var A = getDomainFast(indexA);
    var B = getDomainFast(indexB);
    var R = getDomainFast(indexR);
    TRACE(' = min_div', indexR, '=', indexA, '*', indexB, '   ->   ', domain__debug(R), '=', domain__debug(A), '/', domain__debug(B));
    if (!A || !B || !R) return; // R = A / B, A = R * B, B = A / R
    // note:  A / B = C   ==>   <loA / hiB, hiA / loB> and has rounding/div-by-zero issues!
    // but: A * B = C   ==>   <loA * loB, hiA * hiB> use "inv-div" tactic
    // basically remove any value from the domains that can not lead to a valid integer result A/B=C

    TRACE(' - div propagation step...', domain__debug(R), '=', domain__debug(A), '/', domain__debug(B));
    var oR = R;
    R = domain_intersection(R, domain_divby(A, B));
    TRACE(' ->', 'R:', domain__debug(R), '=', 'A:', domain__debug(A), '/', 'B:', domain__debug(B));
    if (R !== oR) updateDomain(indexR, R, 'div R');
    if (!A || !B || !R) return;
    TRACE(' - domains;', domain__debug(R), '=', domain__debug(A), '/', domain__debug(B));

    if (domain_isSolved(B) && domain_isSolved(A)) {
      ASSERT(domain_isSolved(R), 'if A and B are solved then R should be solved');
      ml_eliminate(ml, offset, SIZEOF_VVV);
    } else {
      TRACE(' - not only jumps...');
      onlyJumps = false;
      pc = offset + SIZEOF_VVV;
    }
  }

  function min_isSame(ml, offset) {
    var argCount = ml_dec16(ml, offset + 1);
    TRACE(' = min_isSame, arg count:', argCount);

    if (argCount !== 2) {
      TRACE(' - argcount !== 2 so bailing for now');
      TRACE(' - not only jumps...');
      onlyJumps = false;
      pc = offset + SIZEOF_C + argCount * 2 + 2;
      return;
    }

    var offsetA = offset + OFFSET_C_A;
    var offsetB = offset + OFFSET_C_B;
    var offsetR = offset + OFFSET_C_R;
    var indexA = readIndex(ml, offsetA);
    var indexB = readIndex(ml, offsetB);
    var indexR = readIndex(ml, offsetR);
    var A = getDomainFast(indexA);
    var B = getDomainFast(indexB);
    var R = getDomainFast(indexR);
    TRACE(' - min_isSame', indexR, '=', indexA, '==?', indexB, '   ->   ', domain__debug(R), '=', domain__debug(A), '==?', domain__debug(B));
    if (!A || !B || !R) return;

    if (indexA === indexB) {
      TRACE(' - indexA == indexB so forcing R to 1 and removing constraint');
      var oR = R;
      R = domain_removeValue(R, 0);
      if (R !== oR) updateDomain(indexR, R, 'issame R: A!=B');
      ASSERT(ml_dec16(ml, offset + 1) === 2, 'arg count should be 2 here');
      ml_eliminate(ml, offset, SIZEOF_CR_2);
      return;
    }

    var vA = domain_getValue(A);
    var vB = domain_getValue(B);

    if (vA >= 0 && vB >= 0) {
      TRACE(' - A and B are solved so we can determine R and eliminate the constraint');
      var _oR5 = R;

      if (A === B) {
        R = domain_removeValue(R, 0);
        if (R !== _oR5) updateDomain(indexR, R, 'issame R: A==B');
      } else {
        R = domain_intersectionValue(R, 0);
        if (R !== _oR5) updateDomain(indexR, R, 'issame R: A!=B');
      }

      ASSERT(ml_dec16(ml, offset + 1) === 2, 'arg count should be 2 here');
      ml_eliminate(ml, offset, SIZEOF_CR_2);
      return;
    } // A and B arent both solved. check R


    if (domain_isZero(R)) {
      TRACE(' ! R=0 while A or B isnt solved, changing issame to diff and revisiting');
      ASSERT(ml_dec16(ml, offset + 1) === 2, 'arg count should be 2 here');
      ml_cr2c2(ml, offset, 2, ML_DIFF, indexA, indexB);
      varChanged = true;
      return;
    }

    if (domain_hasNoZero(R)) {
      TRACE(' ! R>=1 while A or B isnt solved, aliasing A to B, eliminating constraint');
      intersectAndAlias(indexA, indexB, A, B);
      ASSERT(ml_dec16(ml, offset + 1) === 2, 'arg count should be 2 here');
      ml_eliminate(ml, offset, SIZEOF_CR_2);
      varChanged = true;
      return;
    }

    if (indexA === indexB) {
      TRACE(' ! index A === index B so R should be truthy and we can eliminate the constraint');
      var _oR6 = R;
      R = domain_removeValue(R, 0);
      if (R !== _oR6) updateDomain(indexR, R, 'issame R: A==B');
      ASSERT(ml_dec16(ml, offset + 1) === 2, 'arg count should be 2 here');
      ml_eliminate(ml, offset, SIZEOF_CR_2);
      return;
    }

    if (!domain_intersection(A, B)) {
      TRACE(' - no overlap between', indexA, 'and', indexB, ' (', domain__debug(A), domain__debug(B), ') so R becomes 0 and constraint is removed');
      var _oR7 = R;
      R = domain_removeGtUnsafe(R, 0);
      if (R !== _oR7) updateDomain(indexR, R, 'issame; no overlap A B so R=0');
      ASSERT(ml_dec16(ml, offset + 1) === 2, 'arg count should be 2 here');
      ml_eliminate(ml, offset, SIZEOF_CR_2);
      return;
    } // There are some bool-domain-specific tricks we can apply
    // TODO: shouldnt these also confirm that A and/or B are actually solved? and not -1


    if (domain_isBool(R)) {
      // If A=0|1, B=[0 1], R=[0 1] we can recompile this to DIFF or SAME
      if (vA >= 0 && vA <= 1 && domain_isBool(B)) {
        TRACE(' ! [01]=0|1==?[01] so morphing to n/eq and revisiting');
        ASSERT(ml_dec16(ml, offset + 1) === 2, 'arg count should be 2 here'); // - A=0: 0==A=1, 1==A=0: B!=R
        // - A=1: 0==A=0, 1==A=1: B==R

        if (vA === 0) {
          TRACE('   - morphing constraint to diff');
          ml_cr2c2(ml, offset, 2, ML_DIFF, indexB, indexR);
        } else {
          TRACE('   - aliasing R to B, eliminating constraint');
          intersectAndAlias(indexR, indexB, R, B);
          ml_eliminate(ml, offset, SIZEOF_CR_2);
        }

        varChanged = true;
        return;
      } // If A=[0 1], B=0|1, R=[0 1] we can recompile this to DIFF or SAME


      if (vB >= 0 && vB <= 1 && domain_isBool(A)) {
        TRACE(' ! [01]=[01]==?0|1 so morphing to n/eq and revisiting');
        ASSERT(ml_dec16(ml, offset + 1) === 2, 'arg count should be 2 here'); // - B=0: 0==B=1, 1==B=0: A!=R
        // - B=1: 0==B=0, 1==B=1: A==R

        if (vB === 0) {
          TRACE('   - morphing constraint to diff');
          ml_cr2c2(ml, offset, 2, ML_DIFF, indexA, indexR);
        } else {
          TRACE('   - aliasing R to A, eliminating constraint');
          intersectAndAlias(indexR, indexA, R, A);
          ml_eliminate(ml, offset, SIZEOF_CR_2);
        }

        varChanged = true;
        return;
      } // Note: cant do XNOR trick here because that only works on BOOLY vars

    }

    if (vA === 0) {
      // This means R^B
      TRACE(' ! A=0 so R^B, morphing to xor');
      ASSERT(ml_dec16(ml, offset + 1) === 2, 'arg count should be 2 here');
      ml_cr2c2(ml, offset, 2, ML_XOR, indexR, indexB);
      varChanged = true;
      return;
    }

    if (vB === 0) {
      // This means R^A
      TRACE(' ! B=0 so R^A, morphing to xor');
      ASSERT(ml_dec16(ml, offset + 1) === 2, 'arg count should be 2 here');
      ml_cr2c2(ml, offset, 2, ML_XOR, indexR, indexA);
      varChanged = true;
      return;
    }

    TRACE(' ->', domain__debug(R), '=', domain__debug(A), '==?', domain__debug(B));
    ASSERT(domain_min(R) === 0 && domain_max(R) > 0, 'R should be a booly at this point', domain__debug(R));
    TRACE(' - not only jumps...');
    ASSERT(ml_dec16(ml, offset + 1) === 2, 'arg count should be 2 here');
    onlyJumps = false;
    pc = offset + SIZEOF_CR_2;
  }

  function min_isDiff(ml, offset) {
    var argCount = ml_dec16(ml, offset + 1);
    TRACE(' = min_isDiff; argCount=', argCount);

    if (argCount !== 2) {
      TRACE(' - count != 2, bailing for now');
      TRACE(' - not only jumps...');
      onlyJumps = false;
      pc = offset + SIZEOF_C + argCount * 2 + 2;
      return;
    }

    var offsetA = offset + OFFSET_C_A;
    var offsetB = offset + OFFSET_C_B;
    var offsetR = offset + OFFSET_C_R;
    var indexA = readIndex(ml, offsetA);
    var indexB = readIndex(ml, offsetB);
    var indexR = readIndex(ml, offsetR);
    var A = getDomainFast(indexA);
    var B = getDomainFast(indexB);
    var R = getDomainFast(indexR);
    TRACE(' = min_isDiff', indexR, '=', indexA, '!=?', indexB, '   ->   ', domain__debug(R), '=', domain__debug(A), '!=?', domain__debug(B));
    if (!A || !B || !R) return;

    if (domain_isSolved(A) && domain_isSolved(B)) {
      TRACE(' - A and B are solved so we can determine R');
      var oR = R;

      if (A === B) {
        R = domain_removeGtUnsafe(R, 0);
        if (R !== oR) updateDomain(indexR, R, 'isdiff R; A==B');
      } else {
        R = domain_removeValue(R, 0);
        if (R !== oR) updateDomain(indexR, R, 'isdiff R; A!=B');
      }

      ml_eliminate(ml, offset, SIZEOF_CR_2);
      return;
    } // R should be 0 if A==B. R should be >0 if A!==B


    if (domain_isZero(R)) {
      TRACE(' ! R=0, aliasing A to B, eliminating constraint');
      intersectAndAlias(indexA, indexB, A, B);
      ml_eliminate(ml, offset, SIZEOF_CR_2);
      varChanged = true;
      return;
    }

    if (domain_hasNoZero(R)) {
      TRACE(' ! R>0, changing isdiff to diff and revisiting');
      ml_cr2c2(ml, offset, 2, ML_DIFF, indexA, indexB);
      varChanged = true;
      return;
    }

    TRACE(' ->', domain__debug(R), '=', domain__debug(A), '!=?', domain__debug(B));
    TRACE(' - not only jumps...');
    ASSERT(domain_min(R) === 0 && domain_max(R) >= 1, 'R should be boolable at this point');
    onlyJumps = false;
    pc = offset + SIZEOF_CR_2;
  }

  function min_isLt(ml, offset) {
    var offsetA = offset + 1;
    var offsetB = offset + 3;
    var offsetR = offset + 5;
    var indexA = readIndex(ml, offsetA);
    var indexB = readIndex(ml, offsetB);
    var indexR = readIndex(ml, offsetR);
    var A = getDomainFast(indexA);
    var B = getDomainFast(indexB);
    var R = getDomainFast(indexR);
    TRACE(' = min_isLt', indexR, '=', indexA, '<?', indexB, '   ->   ', domain__debug(R), '=', domain__debug(A), '<?', domain__debug(B));
    if (!A || !B || !R) return;
    var oR = R;

    if (!domain_isSolved(R)) {
      if (domain_max(A) < domain_min(B)) R = domain_removeValue(R, 0);else if (domain_min(A) >= domain_max(B)) R = domain_removeGtUnsafe(R, 0);
    }

    if (R !== oR && !updateDomain(indexR, R, 'islt; solving R because A < B or A >= B')) return; // If R is solved replace this isLt with an lt or "gt" and repeat.
    // the appropriate op can then prune A and B accordingly.
    // in this context, the inverse for lt is an lte with swapped args

    if (domain_isZero(R)) {
      TRACE(' ! result var solved to 0 so compiling an lte with swapped args in its place', indexB, 'and', indexA);
      ml_vvv2c2(ml, offset, ML_LTE, indexB, indexA);
      varChanged = true;
      return;
    }

    if (domain_hasNoZero(R)) {
      TRACE(' ! result var solved to 1 so compiling an lt in its place for', indexA, 'and', indexB);
      ml_vvv2c2(ml, offset, ML_LT, indexA, indexB);
      varChanged = true;
      return;
    }

    if (domain_isZero(A)) {
      TRACE(' - A=0 ! R=0<?B [01]=0<?[0 10] so if B=0 then R=0 and otherwise R=1 so xnor');
      TRACE_MORPH('R=0<?B', 'R!^B');
      ml_vvv2c2(ml, offset, ML_XNOR, indexR, indexB);
      varChanged = true;
      return;
    }

    if (domain_isZero(B)) {
      TRACE(' - B=0 ! so thats just false');
      TRACE_MORPH('R=A<?0', 'R=0');
      ml_eliminate(ml, offset, SIZEOF_VVV);
      return;
    }

    TRACE(' - not only jumps...');
    onlyJumps = false;
    pc = offset + SIZEOF_VVV;
  }

  function min_isLte(ml, offset) {
    var offsetA = offset + 1;
    var offsetB = offset + 3;
    var offsetR = offset + 5;
    var indexA = readIndex(ml, offsetA);
    var indexB = readIndex(ml, offsetB);
    var indexR = readIndex(ml, offsetR);
    var A = getDomainFast(indexA);
    var B = getDomainFast(indexB);
    var R = getDomainFast(indexR);
    TRACE(' = min_isLte', indexR, '=', indexA, '<=?', indexB, '   ->   ', domain__debug(R), '=', domain__debug(A), '<=?', domain__debug(B));
    if (!A || !B || !R) return;
    var oR = R;
    TRACE(' - max(A) <= min(B)?', domain_max(A), '<=', domain_min(B));
    TRACE(' - min(A) > max(B)?', domain_min(A), '>', domain_max(B)); // If R isn't resolved you can't really update A or B. so we don't.

    if (domain_max(A) <= domain_min(B)) R = domain_removeValue(R, 0);else if (domain_min(A) > domain_max(B)) R = domain_removeGtUnsafe(R, 0);

    if (R !== oR) {
      TRACE(' - updated R to', domain__debug(R));
      if (updateDomain(indexR, R, 'islte; solving R because A and B are solved')) return;
    }

    var falsyR = domain_isZero(R);
    var truthyR = falsyR ? false : domain_hasNoZero(R); // If R is resolved replace this isLte with an lte or "gte" and repeat.
    // the appropriate op can then prune A and B accordingly.
    // in this context, the logical inverse for lte is an lt with swapped args

    if (falsyR) {
      TRACE(' ! result var solved to 0 so compiling an lt with swapped args in its place', indexB, 'and', indexA);
      ml_vvv2c2(ml, offset, ML_LT, indexB, indexA);
      varChanged = true;
      return;
    }

    if (truthyR) {
      TRACE(' ! result var solved to 1 so compiling an lte in its place', indexA, 'and', indexB);
      ml_vvv2c2(ml, offset, ML_LTE, indexA, indexB);
      varChanged = true;
      return;
    } // TODO: C=A<=?B   ->   [01] = [11] <=? [0 n]   ->   B !^ C


    if (domain_isBool(R) && domain_max(A) <= 1 && domain_max(B) <= 1) {
      TRACE(' - R is bool and A and B are bool-bound so checking bool specific cases');
      ASSERT(!domain_isZero(A) || !domain_isBool(B), 'this case should be caught by max<min checks above');

      if (domain_isBool(A) && domain_isZero(B)) {
        TRACE_MORPH('[01] = [01] <=? 0', 'A != R');
        ml_vvv2c2(ml, offset, ML_DIFF, indexA, indexR);
        varChanged = true;
        return;
      }

      if (domain_isBool(A) && B === domain_createValue(1)) {
        TRACE_MORPH('[01] = [01] <=? 1', 'A == R');
        intersectAndAlias(indexA, indexR, A, R);
        ml_eliminate(ml, offset, SIZEOF_VVV);
        varChanged = true;
        return;
      }

      if (domain_isBool(B) && A === domain_createValue(1)) {
        TRACE_MORPH('[01] = 1 <=? [01]', 'B == R');
        intersectAndAlias(indexB, indexR, B, R);
        ml_eliminate(ml, offset, SIZEOF_VVV);
        varChanged = true;
        return;
      }
    }

    TRACE(' - not only jumps...');
    onlyJumps = false;
    pc = offset + SIZEOF_VVV;
  }

  function min_sum(ml, offset) {
    var offsetCount = offset + 1;
    var argCount = ml_dec16(ml, offsetCount);

    if (argCount === 2) {
      if (min_sum_2(ml, offset)) return; // TOFIX: merge with this function...?
    }

    var opSize = SIZEOF_C + argCount * 2 + 2;
    var offsetArgs = offset + SIZEOF_C;
    var offsetR = offset + opSize - 2;
    var indexR = readIndex(ml, offsetR);
    var R = getDomainFast(indexR);
    TRACE(' = min_sum', argCount, 'x');
    TRACE('  - ml for this sum:', ml.slice(offset, offset + opSize).join(' '));
    TRACE('  - indexes:', indexR, '= sum(', [].concat(Array(argCount)).map(function (n, i) {
      return readIndex(ml, offsetArgs + i * 2);
    }).join(', '), ')');
    TRACE('  - domains:', domain__debug(R), '= sum(', [].concat(Array(argCount)).map(function (n, i) {
      return domain__debug(getDomainFast(readIndex(ml, offsetArgs + i * 2)));
    }).join(', '), ')');
    if (!R) return; // A sum is basically a pyramid of plusses; (A+B)+(C+D) etc
    // we loop back to front because we're splicing out vars while looping
    // replace all constants by one constant
    // prune the result var by intersecting it with the sum of the actual args
    // in limited cases we can prune some of the arg values if the result forces
    // that (if the result is max 10 then inputs can be pruned of any value > 10)
    // we cant really do anything else

    TRACE(' - first loop to get the sum of the args and constants');
    var sum = domain_createValue(0);
    var constants = 0;
    var constantSum = 0;

    for (var i = 0; i < argCount; ++i) {
      var argOffset = offsetArgs + i * 2;
      var index = readIndex(ml, argOffset);
      var domain = getDomainFast(index);
      TRACE('    - i=', i, ', offset=', argOffset, ', index=', index, 'dom=', domain__debug(domain), ', constants before:', constants, 'sum of constant before:', constantSum);
      var v = domain_getValue(domain);

      if (v >= 0) {
        TRACE('      - this is a constant! value =', v);
        ++constants;
        constantSum += v;
      }

      sum = domain_plus(sum, domain);
    }

    TRACE(' - total sum=', domain__debug(sum), ', constantSum=', constantSum, 'with', constants, 'constants. applying to R', domain__debug(R), '=>', domain__debug(domain_intersection(sum, R)));
    var oR = R;

    if (constants === argCount) {
      // Bit of an edge case, though it can happen after multiple passes
      TRACE(' - all sum args are constants so R must simply eq their sum, eliminating constraint');
      R = domain_intersectionValue(R, constantSum);
      if (R !== oR) updateDomain(indexR, R, 'setting R to sum of constants');
      ml_eliminate(ml, offset, opSize);
      return;
    }

    R = domain_intersection(sum, R);
    TRACE(' - Updated R from', domain__debug(oR), 'to', domain__debug(R));
    if (R !== oR && updateDomain(indexR, R, 'sum; updating R with outer bounds of its args;')) return;
    ASSERT(constantSum <= domain_max(R), 'the sum of constants should not exceed R', constantSum); // Get R without constants to apply to var args

    var subR = constantSum ? domain_minus(R, domain_createValue(constantSum)) : R;
    ASSERT(subR, 'R-constants should not be empty', constantSum);
    TRACE(' - Now back propagating R to the args. R-constants:', domain__debug(subR)); // Have to count constants and sum again because if a var occurs twice and this
    // updates it to a constant, the second one would otherwise be missed as old.

    constants = 0;
    constantSum = 0; // We can only trim bounds, not a full intersection (!)
    // note that trimming may lead to more constants so dont eliminate them here (KIS)

    var minSR = domain_min(subR);
    var maxSR = domain_max(subR);
    var varIndex1 = -1; // Track non-constants for quick optimizations for one or two vars

    var varIndex2 = -1;

    for (var _i6 = 0; _i6 < argCount; ++_i6) {
      var _index6 = readIndex(ml, offsetArgs + _i6 * 2);

      var _domain8 = getDomainFast(_index6);

      TRACE('    - i=', _i6, ', index=', _index6, 'dom=', domain__debug(_domain8));

      var _v = domain_getValue(_domain8);

      if (_v >= 0) {
        TRACE('      - old constant (or var that occurs twice and is now a new constant)', _v);
        ++constants;
        constantSum += _v;
      } else {
        // So the idea is that any value in an arg that could not even appear in R if all other args
        // were zero, is a value that cant ever yield a solution. those are the values we trim here.
        // this process takes constants in account (hence subR) because they don't have a choice.
        var newDomain = domain_removeLtUnsafe(_domain8, minSR);
        newDomain = domain_removeGtUnsafe(_domain8, maxSR);
        if (newDomain !== _domain8 && updateDomain(_index6, newDomain, 'plus arg; trim invalid values')) return;
        _v = domain_getValue(newDomain);

        if (_v >= 0) {
          TRACE('      - new constant', _v); // Arg is NOW also a constant

          ++constants;
          constantSum += _v;
        } else if (varIndex1 === -1) {
          TRACE('      - first non-constant');
          varIndex1 = _index6;
        } else if (varIndex2 === -1) {
          TRACE('      - second non-constant');
          varIndex2 = _index6;
        }
      }
    }

    TRACE(' -> There are now', constants, 'constants and', argCount - constants, 'actual vars. Constants sum to', constantSum, ', R=', domain__debug(R));
    TRACE(' -> Current args: ', [].concat(Array(argCount)).map(function (n, i) {
      return domain__debug(getDomainFast(readIndex(ml, offsetArgs + i * 2)));
    }).join(' '), ' Result:', domain__debug(R));
    var valuesToSumLeft = argCount - constants + (constantSum === 0 ? 0 : 1);
    TRACE(' - args:', argCount, ', constants:', constants, ', valuesToSumLeft=', valuesToSumLeft, ', constantSum=', constantSum, ', varIndex1=', varIndex1, ', varIndex2=', varIndex2);
    ASSERT(valuesToSumLeft > 0 || constantSum === 0 && argCount === constants, 'a sum with args cant have no values left here unless there are only zeroes (it implies empty domains and should incur early returns)', valuesToSumLeft);

    if (valuesToSumLeft === 1) {
      // ignore constants if they are zero!
      TRACE(' - valuesToSumLeft = 1');
      ASSERT(varIndex2 === -1, 'we shouldnt have found a second var', varIndex2);
      ASSERT(constantSum > 0 ? varIndex1 === -1 : varIndex1 >= 0, 'with one value left it should either be a nonzero constant or an actual variable');

      if (constantSum > 0) {
        TRACE(' - Setting R to the sum of constants:', constantSum);
        var nR = domain_intersectionValue(R, constantSum);
        if (nR !== R) updateDomain(indexR, nR, 'min_sum');
      } else {
        TRACE(' - Aliasing R to the single var', varIndex1);
        intersectAndAlias(indexR, varIndex1, R, getDomain(varIndex1, true));
      }

      TRACE(' - eliminating constraint now');
      ml_eliminate(ml, offset, opSize);
    } else if (constants > 1 || constants === 1 && constantSum === 0) {
      TRACE(' - valuesToSumLeft > 1. Unable to morph but there are', constants, 'constants to collapse to a single arg with value', constantSum); // There are constants and they did not morph or eliminate the constraint; consolidate them.
      // loop backwards, remove all constants except one, move all other args back to compensate,
      // only update the index of the last constant, update the count, compile a jump for the new trailing space

      var newOpSize = opSize - (constants - (constantSum > 0 ? 1 : 0)) * 2;

      for (var _i7 = argCount - 1; _i7 >= 0 && constants; --_i7) {
        var _argOffset = offsetArgs + _i7 * 2;

        var _index7 = readIndex(ml, _argOffset);

        var _domain9 = getDomainFast(_index7);

        TRACE('    - i=', _i7, ', index=', _index7, 'dom=', domain__debug(_domain9));

        if (domain_isSolved(_domain9)) {
          if (constants === 1 && constantSum !== 0) {
            // If constantSum>0 then we should encounter at least one constant to do this step on
            TRACE('      - Overwriting the last constant at', _argOffset, 'with an index for total constant value', constantSum);
            var newConstantIndex = addVar(undefined, constantSum, false, false, true);
            ml_enc16(ml, offsetArgs + _i7 * 2, newConstantIndex);
            break; // Probably not that useful, might even be bad to break here
          } else {
            TRACE('      - found a constant to remove at', _argOffset, ', moving further domains one space forward (from ', _i7 + 1, ' / ', argCount, ')', _i7 + 1 < argCount);
            ASSERT(constants > 0, 'should have some constants');
            min_spliceArgSlow(ml, offsetArgs, argCount, _i7, true); // Also moves R

            --argCount;
          }

          --constants;
        }
      }

      ml_enc16(ml, offset + 1, argCount); // Now "blank out" the space of eliminated constants, they should be at the end of the op

      ml_compileJumpSafe(ml, offset + newOpSize, opSize - newOpSize);
      TRACE(' - Cleaned up constant args');
      TRACE(' - ml for this sum now:', ml.slice(offset, offset + opSize).join(' '));
    } else {
      TRACE(' - unable to improve this sum at this time');
      TRACE(' - not only jumps...');
      onlyJumps = false;
      pc = offset + opSize;
    }
  }

  function min_spliceArgSlow(ml, argsOffset, argCount, argIndex, includingResult) {
    TRACE('      - min_spliceArgSlow(', argsOffset, argCount, argIndex, includingResult, ')');
    var toCopy = argCount;
    if (includingResult) ++toCopy;

    for (var i = argIndex + 1; i < toCopy; ++i) {
      var fromOffset = argsOffset + i * 2;
      var toOffset = argsOffset + (i - 1) * 2;
      TRACE('        - moving', includingResult && i === argCount - 1 ? 'R' : 'arg ' + (i + (includingResult ? 0 : 1)) + '/' + argCount, 'at', fromOffset, 'and', fromOffset + 1, 'moving to', toOffset, 'and', toOffset + 1);
      ml[toOffset] = ml[fromOffset];
      ml[toOffset + 1] = ml[fromOffset + 1];
    }
  }

  function min_product(ml, offset) {
    var offsetCount = offset + 1;
    var argCount = ml_dec16(ml, offsetCount);
    TRACE(' = min_product', argCount, 'x');

    if (argCount === 2) {
      // TODO: merge this
      if (min_product_2(ml, offset)) return;
    }

    var opSize = SIZEOF_C + argCount * 2 + 2;
    var offsetArgs = offset + SIZEOF_C;
    var offsetR = offset + opSize - 2;
    var indexR = readIndex(ml, offsetR);
    var R = getDomainFast(indexR);
    TRACE('  - ml for this product:', ml.slice(offset, offset + opSize).join(' '));
    TRACE('  - indexes:', indexR, '= product(', [].concat(Array(argCount)).map(function (n, i) {
      return readIndex(ml, offsetArgs + i * 2);
    }).join(', '), ')');
    TRACE('  - domains:', domain__debug(R), '= product(', [].concat(Array(argCount)).map(function (n, i) {
      return domain__debug(getDomainFast(readIndex(ml, offsetArgs + i * 2)));
    }).join(', '), ')');
    if (!R) return; // A product is basically a pyramid of muls; (A*B)*(C*D) etc
    // we loop back to front because we're splicing out vars while looping
    // replace all constants by one constant
    // prune the result var by intersecting it with the product of the actual args
    // in limited cases we can prune some of the arg values if the result forces
    // that (if the result is max 10 then inputs can be pruned of any value > 10)
    // we cant really do anything else

    TRACE(' - first loop to get the product of the args and constants');
    var product = domain_createValue(1);
    var constants = 0;
    var constantProduct = 1;

    for (var i = 0; i < argCount; ++i) {
      var index = readIndex(ml, offsetArgs + i * 2);
      var domain = getDomainFast(index);
      TRACE('    - i=', i, ', index=', index, 'dom=', domain__debug(domain), ', constant product before:', constantProduct);
      var v = domain_getValue(domain);

      if (v >= 0) {
        ++constants;
        constantProduct *= v;
      }

      product = domain_mul(product, domain);
    }

    TRACE(' - total product=', domain__debug(product), ', constantProduct=', constantProduct, 'with', constants, 'constants. applying to R', domain__debug(R), '=', domain__debug(domain_intersection(product, R)));
    var oR = R;

    if (constants === argCount) {
      // Bit of an edge case, though it can happen after multiple passes
      TRACE(' - all product args are constants so R must simply eq their product, eliminating constraint;', domain__debug(R), '&', domain__debug(domain_createValue(constantProduct)), '=', domain__debug(domain_intersectionValue(R, constantProduct)));
      R = domain_intersectionValue(R, constantProduct);
      if (R !== oR) updateDomain(indexR, R, 'setting R to product of constants');
      ml_eliminate(ml, offset, opSize);
      return;
    }

    if (constantProduct === 0) {
      // Edge case; if a constant produced zero then R will be zero and all args are free
      TRACE(' - there was a zero constant so R=0 and all args are free, eliminating constraint');
      R = domain_intersectionValue(R, 0);
      if (R !== oR) updateDomain(indexR, R, 'setting R to zero');
      ml_eliminate(ml, offset, opSize);
      return;
    }

    R = domain_intersection(product, R);
    TRACE(' - Updated R from', domain__debug(oR), 'to', domain__debug(R));
    if (R !== oR && updateDomain(indexR, R, 'product; updating R with outer bounds of its args;')) return;

    if (domain_isZero(R)) {
      TRACE(' - R=0 so at least one arg must be 0, morph this to a nall');
      ml_enc8(ml, offset, ML_NALL);
      ml_compileJumpSafe(ml, offset + opSize - 2, 2); // Cuts off R

      return;
    } // From this point R isnt zero and none of the args is solved to zero (but could still have it in their domain!)
    // this simplifies certain decisions :)


    ASSERT(domain_invMul(R, constantProduct), 'R should be a multiple of the constant sum');
    ASSERT(domain_min(R) === 0 || Number.isFinite(domain_min(R) / constantProduct), 'min(R) should be the result of the constants multiplied by other values, so dividing it should result in an integer');
    ASSERT(Number.isFinite(domain_max(R) / constantProduct), 'max(R) should be the result of the constants multiplied by other values, so dividing it should result in an integer'); // Get R without constants to apply to var args

    var subR = constantProduct === 1 ? R : domain_invMul(R, domain_createValue(constantProduct));
    ASSERT(subR, 'R-constants should not be empty');
    TRACE(' - Now back propagating R to the args, R without constants:', domain__debug(subR)); // We can only trim bounds, not a full intersection (!)
    // note that trimming may lead to more constants so dont eliminate them here (KIS)

    var minSR = domain_min(subR);
    var maxSR = domain_max(subR);
    var atLeastOneArgHadZero = false; // Any zero can blow up the result to 0, regardless of other args

    var varIndex1 = -1; // Track non-constants for quick optimizations for one or two vars

    var varIndex2 = -1;

    for (var _i8 = 0; _i8 < argCount; ++_i8) {
      var _index8 = readIndex(ml, offsetArgs + _i8 * 2);

      var _domain10 = getDomainFast(_index8);

      TRACE('    - i=', _i8, ', index=', _index8, 'dom=', domain__debug(_domain10));

      var _v2 = domain_getValue(_domain10);

      if (_v2 === 0) atLeastOneArgHadZero = true; // Probably not very useful

      if (_v2 < 0) {
        // ignore constants
        if (!atLeastOneArgHadZero && domain_hasZero(_domain10)) atLeastOneArgHadZero = true; // So the idea is that any value in an arg that could not even appear in R if all other args
        // were zero, is a value that cant ever yield a solution. those are the values we trim here.
        // this process takes constants in account (hence subR) because they don't have a choice.

        var newDomain = domain_removeLtUnsafe(_domain10, minSR);
        newDomain = domain_removeGtUnsafe(_domain10, maxSR);
        if (newDomain !== _domain10 && updateDomain(_index8, newDomain, 'product arg; trim invalid values')) return;
        _v2 = domain_getValue(newDomain);

        if (_v2 >= 0) {
          TRACE('      - constant', _v2); // Arg is NOW also a constant

          ++constants;
          constantProduct += _v2;
        } else if (varIndex1 === -1) {
          TRACE('      - first non-constant');
          varIndex1 = _index8;
        } else if (varIndex2 === -1) {
          TRACE('      - second non-constant');
          varIndex2 = _index8;
        }
      }
    }

    TRACE(' -> There are now', constants, 'constants and', argCount - constants, 'actual vars. Constants mul to', constantProduct, ', R=', domain__debug(R));
    TRACE(' -> Current args: ', [].concat(Array(argCount)).map(function (n, i) {
      return domain__debug(getDomainFast(readIndex(ml, offsetArgs + i * 2)));
    }).join(' '), ' Result:', domain__debug(R));
    var valuesToMulLeft = argCount - constants + (constantProduct === 1 ? 0 : 1);
    ASSERT(valuesToMulLeft > 0 || constantProduct === 1 && argCount === constants, 'a product with args cant have no values left here unless the constants are all 1 (it implies empty domains and should incur early returns)', valuesToMulLeft);

    if (valuesToMulLeft === 1) {
      // ignore constants if they are zero!
      ASSERT(varIndex2 === -1, 'we shouldnt have found a second var', varIndex2);

      if (constantProduct !== 1) {
        TRACE(' - Setting R to the product of constants:', constantProduct, '(and a zero?', atLeastOneArgHadZero, ')');

        if (atLeastOneArgHadZero) {
          TRACE('   - Updating to a booly-pair:', domain__debug(domain_createBoolyPair(constantProduct)));
          var nR = domain_intersection(R, domain_createBoolyPair(constantProduct));
          if (nR !== R) updateDomain(indexR, nR, 'min_product');
        } else {
          TRACE('   - Updating to a solved value:', constantProduct);

          var _nR = domain_intersectionValue(R, constantProduct);

          if (_nR !== R) updateDomain(indexR, _nR, 'min_product');
        }
      } else {
        TRACE(' - Aliasing R to the single var', varIndex1);
        intersectAndAlias(indexR, varIndex1, R, getDomain(varIndex1, true));
      }

      TRACE(' - eliminating constraint now');
      ml_eliminate(ml, offset, opSize);
    } else if (constants > 1) {
      TRACE(' - Unable to morph but there are', constants, 'constants to collapse to a single arg with value', constantProduct); // There are constants and they did not morph or eliminate the constraint; consolidate them.
      // loop backwards, remove all constants except one, move all other args back to compensate,
      // only update the index of the last constant, update the count, compile a jump for the new trailing space

      var newOpSize = opSize - (constants - 1) * 2;

      for (var _i9 = argCount - 1; _i9 >= 0 && constants; --_i9) {
        var _index9 = readIndex(ml, offsetArgs + _i9 * 2);

        var _domain11 = getDomainFast(_index9);

        TRACE('    - i=', _i9, ', index=', _index9, 'dom=', domain__debug(_domain11), ', constant?', domain_isSolved(_domain11));

        if (domain_isSolved(_domain11)) {
          if (constants === 1) {
            TRACE(' - Overwriting the last constant with an index for the total constant value');

            var _index10 = addVar(undefined, constantProduct, false, false, true);

            ml_enc16(ml, offsetArgs + _i9 * 2, _index10);
          } else {
            TRACE('  - found a constant, moving further domains one space forward (from ', _i9 + 1, ' / ', argCount, ')', _i9 + 1 < argCount);
            ASSERT(constants > 0, 'should have some constants');
            min_spliceArgSlow(ml, offsetArgs, argCount, _i9, true); // Move R as well

            --argCount;
          }

          --constants;
        }
      }

      var emptySpace = opSize - newOpSize;
      TRACE(' - constants squashed, compiling new length (', argCount, ') and a jump for the empty space (', emptySpace, 'bytes )');
      ml_enc16(ml, offset + 1, argCount); // Now "blank out" the space of eliminated constants, they should be at the end of the op

      ASSERT(emptySpace > 0, 'since at least two constants were squashed there should be some bytes empty now');
      ml_compileJumpSafe(ml, offset + newOpSize, emptySpace);
      TRACE(' - ml for this product now:', ml.slice(offset, offset + opSize).join(' '));
      ASSERT(ml_validateSkeleton(ml, 'min_product; case 3'));
      TRACE(' - Cleaned up constant args');
    } else {
      TRACE(' - not only jumps...');
      onlyJumps = false;
      pc = offset + opSize;
    }
  }

  function min_all(ml, offset) {
    // Loop through the args and remove zero from all of them. then eliminate the constraint. it is an artifact.
    var argCount = ml_dec16(ml, offset + 1);
    TRACE(' = min_all', argCount, 'x. removing zero from all args and eliminating constraint');

    for (var i = 0; i < argCount; ++i) {
      var indexD = readIndex(ml, offset + SIZEOF_C + i * 2);
      var oD = getDomain(indexD, true);
      var D = domain_removeValue(oD, 0);
      if (oD !== D) updateDomain(indexD, D, 'ALL D');
    }

    ml_eliminate(ml, offset, SIZEOF_C + argCount * 2);
  }

  function min_some_2(ml, offset) {
    var offsetA = offset + OFFSET_C_A;
    var offsetB = offset + OFFSET_C_B;
    var indexA = readIndex(ml, offsetA);
    var indexB = readIndex(ml, offsetB);
    var A = getDomainFast(indexA);
    var B = getDomainFast(indexB);
    TRACE(' = min_some_2', indexA, '|', indexB, '   ->   ', domain__debug(A), '|', domain__debug(B));
    if (!A || !B) return true;

    if (indexA === indexB) {
      TRACE(' - argcount=2 and indexA==indexB. so A>0 and eliminating constraint');
      var nA = domain_removeValue(A, 0);
      if (A !== nA) updateDomain(indexA, nA, 'A|A');
      ml_eliminate(ml, offset, SIZEOF_C_2);
      return;
    }

    if (domain_isZero(A)) {
      TRACE(' - A=0 so remove 0 from B', domain__debug(B), '->', domain__debug(domain_removeValue(B, 0)));
      var oB = B;
      B = domain_removeValue(oB, 0);
      if (B !== oB) updateDomain(indexB, B, 'OR B');
      ml_eliminate(ml, offset, SIZEOF_C_2);
      return true;
    }

    if (domain_isZero(B)) {
      TRACE(' - B=0 so remove 0 from A', domain__debug(A), '->', domain__debug(domain_removeValue(A, 0)));
      var oA = A;
      A = domain_removeValue(oA, 0);
      if (A !== oA) updateDomain(indexA, A, 'OR A');
      ml_eliminate(ml, offset, SIZEOF_C_2);
      return true;
    }

    if (domain_hasNoZero(A) || domain_hasNoZero(B)) {
      TRACE(' - at least A or B has no zero so remove constraint');
      ml_eliminate(ml, offset, SIZEOF_C_2);
      return true;
    }

    TRACE(' - min_some_2 changed nothing');
    return false;
  }

  function min_none(ml, offset) {
    var argCount = ml_dec16(ml, offset + 1);
    TRACE(' = min_none on', argCount, 'vars. Setting them all to zero and removing constraint.'); // This is an artifact and that is fine.

    for (var i = 0; i < argCount; ++i) {
      var indexD = readIndex(ml, offset + SIZEOF_C + i * 2);
      var D = getDomain(indexD, true);
      var nD = domain_removeGtUnsafe(D, 0);
      if (D !== nD) updateDomain(indexD, nD);
    }

    ml_eliminate(ml, offset, SIZEOF_C + argCount * 2);
  }

  function min_xor(ml, offset) {
    var offsetA = offset + OFFSET_C_A;
    var offsetB = offset + OFFSET_C_B;
    var indexA = readIndex(ml, offsetA);
    var indexB = readIndex(ml, offsetB);
    var A = getDomainFast(indexA);
    var B = getDomainFast(indexB);
    TRACE(' = min_xor', indexA, '^', indexB, '   ->   ', domain__debug(A), '^', domain__debug(B));
    if (!A || !B) return;

    if (indexA === indexB) {
      TRACE(' - index A === index B, x^x is falsum');
      setEmpty(indexA, 'x^x');
      emptyDomain = true;
      return;
    }

    if (domain_isZero(A)) {
      TRACE(' - A=0 so B must be >=1');
      var oB = B;
      B = domain_removeValue(B, 0);
      if (B !== oB) updateDomain(indexB, B, 'xor B>=1');
      ml_eliminate(ml, offset, SIZEOF_C_2);
      return;
    }

    if (domain_isZero(B)) {
      TRACE(' - B=0 so A must be >=1');
      var oA = A;
      A = domain_removeValue(A, 0);
      if (A !== oA) updateDomain(indexA, A, 'xor A>=1');
      ml_eliminate(ml, offset, SIZEOF_C_2);
      return;
    }

    if (domain_hasNoZero(A)) {
      TRACE(' - A>=1 so B must be 0');
      var _oB = B;
      B = domain_removeGtUnsafe(B, 0);
      if (B !== _oB) updateDomain(indexB, B, 'xor B=0');
      ml_eliminate(ml, offset, SIZEOF_C_2);
      return;
    }

    if (domain_hasNoZero(B)) {
      TRACE(' - B>=1 so A must be 0');
      var _oA2 = A;
      A = domain_removeGtUnsafe(A, 0);
      if (A !== _oA2) updateDomain(indexA, A, 'xor A=0');
      ml_eliminate(ml, offset, SIZEOF_C_2);
      return;
    }

    TRACE(' - not only jumps...');
    onlyJumps = false;
    pc = offset + SIZEOF_C_2;
  }

  function min_xnor(ml, offset) {
    var argCount = ml_dec16(ml, offset + 1);
    TRACE(' = min_xnor;', argCount, 'args');

    if (argCount !== 2) {
      TRACE(' - xnor does not have 2 args, bailing for now');
      onlyJumps = false;
      pc = offset + SIZEOF_C + argCount * 2;
      return;
    }

    var offsetA = offset + OFFSET_C_A;
    var offsetB = offset + OFFSET_C_B;
    var indexA = readIndex(ml, offsetA);
    var indexB = readIndex(ml, offsetB);
    var A = getDomainFast(indexA);
    var B = getDomainFast(indexB);
    TRACE(' -', indexA, '!^', indexB, '   ->   ', domain__debug(A), '!^', domain__debug(B));
    if (!A || !B) return;
    ASSERT(ml_dec16(ml, offset + 1) === 2, 'should have 2 args now');

    if (indexA === indexB) {
      TRACE('   - oh... it was the same index. removing op'); // Artifact, can happen

      ml_eliminate(ml, offset, SIZEOF_C_2);
      return;
    }

    if (domain_isZero(A)) {
      TRACE(' - A=0 so B must be 0');
      var oB = B;
      B = domain_removeGtUnsafe(B, 0);
      if (B !== oB) updateDomain(indexB, B, 'xnor B');
      ml_eliminate(ml, offset, SIZEOF_C_2);
      return;
    }

    if (domain_isZero(B)) {
      TRACE(' - B=0 so A must be 0');
      var oA = A;
      A = domain_removeGtUnsafe(A, 0);
      if (A !== oA) updateDomain(indexA, A, 'xnor A');
      ml_eliminate(ml, offset, SIZEOF_C_2);
      return;
    }

    if (domain_hasNoZero(A)) {
      TRACE(' - A>=1 so B must be >=1');
      var _oB2 = B;
      B = domain_removeValue(B, 0);
      if (B !== _oB2) updateDomain(indexB, B, 'xnor B');
      ml_eliminate(ml, offset, SIZEOF_C_2);
      return;
    }

    if (domain_hasNoZero(B)) {
      TRACE(' - B>=1 so A must be >=1');
      var _oA3 = A;
      A = domain_removeValue(A, 0);
      if (A !== _oA3) updateDomain(indexA, A, 'xnor A');
      ml_eliminate(ml, offset, SIZEOF_C_2);
      return;
    } // A and B are booly-pairs and equal then they can be considered an alias


    if (A === B && domain_size(A) === 2) {
      TRACE(' - A==B, size(A)=2 so size(B)=2 so max(A)==max(B) so under XNOR: A==B;', domain__debug(A), '!^', domain__debug(B));
      ASSERT(domain_size(B) === 2, 'If A==B and size(A)=2 then size(B) must also be 2 and they are regular aliases');
      addAlias(indexA, indexB);
      varChanged = true;
      return; // Note: cutter supports more cases for xnor pseudo alias, but that requires knowing BOOLY state for each var
    }

    TRACE(' - not only jumps...');
    onlyJumps = false;
    pc = offset + SIZEOF_C_2;
  }

  function min_imp(ml, offset) {
    var offsetA = offset + OFFSET_C_A;
    var offsetB = offset + OFFSET_C_B;
    var indexA = readIndex(ml, offsetA);
    var indexB = readIndex(ml, offsetB);
    var A = getDomainFast(indexA);
    var B = getDomainFast(indexB);
    TRACE(' = min_imp', indexA, '->', indexB, '   ->   ', domain__debug(A), '->', domain__debug(B));
    if (!A || !B) return;

    if (indexA === indexB) {
      TRACE(' - same index, tautology, eliminating constraint');
      ml_eliminate(ml, offset, SIZEOF_C_2);
      return;
    } // If A is nonzero then B must be nonzero and constraint is solved
    // if A is zero then constraint is solved
    // if B is nonzero then constraint is solved
    // if B is zero then A must be zero


    if (domain_isZero(A)) {
      TRACE(' - A is zero so just eliminate the constraint'); // Eliminate constraint. B is irrelevant now.

      ml_eliminate(ml, offset, SIZEOF_C_2);
      return;
    }

    if (domain_hasNoZero(A)) {
      TRACE(' - A is nonzero so remove zero from B and eliminate the constraint'); // Remove zero from B, eliminate constraint

      var oB = B;
      B = domain_removeValue(oB, 0);
      if (oB !== B) updateDomain(indexB, B, 'IMP B');
      ml_eliminate(ml, offset, SIZEOF_C_2);
      return;
    }

    if (domain_isZero(B)) {
      TRACE(' - B is zero so set A to zero and eliminate the constraint'); // Remove zero from A, eliminate constraint

      var oA = A;
      A = domain_removeGtUnsafe(oA, 0);
      if (oA !== A) updateDomain(indexA, A, 'IMP A');
      ml_eliminate(ml, offset, SIZEOF_C_2);
      return;
    }

    if (domain_hasNoZero(B)) {
      TRACE(' - B is nonzero so just eliminate the constraint'); // Eliminate constraint. A is irrelevant now.

      ml_eliminate(ml, offset, SIZEOF_C_2);
      return;
    }

    TRACE(' - not only jumps...');
    onlyJumps = false;
    pc = offset + SIZEOF_C_2;
  }

  function min_nimp(ml, offset) {
    var offsetA = offset + OFFSET_C_A;
    var offsetB = offset + OFFSET_C_B;
    var indexA = readIndex(ml, offsetA);
    var indexB = readIndex(ml, offsetB);
    var A = getDomainFast(indexA);
    var B = getDomainFast(indexB);
    TRACE(' = min_nimp', indexA, '!->', indexB, '   ->   ', domain__debug(A), '!->', domain__debug(B));
    if (!A || !B) return; // Nimp is trivial since A must be nonzero and B must be zero

    var oA = A;
    A = domain_removeValue(oA, 0);
    if (oA !== A) updateDomain(indexA, A, 'NIMP A');
    var oB = B;
    B = domain_removeGtUnsafe(oB, 0);
    if (oB !== B) updateDomain(indexB, B, 'NIMP B');
    TRACE(' ->', domain__debug(A), '!->', domain__debug(B));
    ml_eliminate(ml, offset, SIZEOF_C_2);
  }
}

var MAX_VAR_COUNT = 0xffff; // 16bit

function $addVar($varTrie, $vars, $domains, $valdist, $constants, $addAlias, $getAnonCounter, $targeted, $targetsFrozen, name, domain, modifier, returnName, returnIndex, _throw) {
  TRACE('addVar', name, domain, modifier, returnName ? '(return name)' : '', returnIndex ? '(return index)' : '');

  if (typeof name === 'number') {
    domain = name;
    name = undefined;
  }

  if (typeof domain === 'number') {
    domain = domain_createValue(domain);
  } else if (domain === undefined) {
    domain = domain_createRange(SUB, SUP);
  } else {
    domain = domain_arrToSmallest(domain);
  }

  var newIndex;
  var v = domain_getValue(domain);

  if (typeof name === 'string' || v < 0 || returnName) {
    var wasAnon = name === undefined;

    if (wasAnon) {
      name = '__' + $getAnonCounter();
      TRACE(' - Adding anonymous var for dom=', domain, '->', name);
    } else if (name[0] === '_' && name[1] === '_' && name === '__' + parseInt(name.slice(2), 10)) {
      THROW('Dont use `__xxx` as var names, that structure is preserved for internal/anonymous var names');
    }

    newIndex = $vars.length;
    var prev = trie_add($varTrie, name, newIndex);

    if (prev >= 0) {
      if (_throw) _throw('CONSTRAINT_VARS_SHOULD_BE_DECLARED; Dont declare a var [' + name + '] after using it', name, prev);
      THROW('CONSTRAINT_VARS_SHOULD_BE_DECLARED; Dont declare a var [' + name + '] after using it', name, prev);
    }

    $vars.push(name);
    $domains.push(domain);
    $targeted[newIndex] = wasAnon ? false : !$targetsFrozen(); // Note: cannot override frozen values since all names must already be declared when using `@custom targets`
  } // Note: if the name is string but domain is constant, we must add the name here as well and immediately alias it to a constant


  if (v >= 0 && !returnName) {
    // TODO: we'll phase out the second condition here soon, but right now constants can still end up as regular vars
    // constants are compiled slightly differently
    var constIndex = value2index($constants, v); // Actual var names must be registered so they can be looked up, then immediately alias them to a constant

    if (newIndex >= 0) $addAlias(newIndex, constIndex, '$addvar');
    newIndex = constIndex;
  }

  if (modifier) {
    $valdist[newIndex] = modifier;

    switch (modifier.valtype) {
      case 'list':
      case 'max':
      case 'mid':
      case 'min':
      case 'minMaxCycle':
      case 'naive':
      case 'splitMax':
      case 'splitMin':
        break;

      default:
        if (_throw) _throw('implement me (var mod [' + modifier.valtype + '])');
        THROW('implement me (var mod [' + modifier.valtype + '])');
    }
  } // Deal with explicitly requested return values...


  if (returnIndex) return newIndex;
  if (returnName) return name;
}

function $name2index($varTrie, $getAlias, name, skipAliasCheck, scanOnly) {
  // ASSERT_LOG2('$name2index', name, skipAliasCheck);
  var varIndex = trie_get($varTrie, name);
  if (!scanOnly && varIndex < 0) THROW('cant use this on constants or vars that have not (yet) been declared', name, varIndex);
  if (!skipAliasCheck && varIndex >= 0) varIndex = $getAlias(varIndex);
  return varIndex;
}

function $addAlias($domains, $valdist, $aliases, $solveStack, $constants, indexOld, indexNew, _origin) {
  TRACE(' - $addAlias' + (_origin ? ' (from ' + _origin + ')' : '') + ': Mapping index = ', indexOld, '(', domain__debug($domains[indexOld]), ') to index = ', indexNew, '(', indexNew >= $domains.length ? 'constant ' + $constants[indexNew] : domain__debug($domains[indexNew]), ')');
  ASSERT(typeof indexOld === 'number', 'old index should be a number', indexOld);
  ASSERT(typeof indexNew === 'number', 'new index should be a number', indexNew);

  if ($aliases[indexOld] === indexNew) {
    TRACE('ignore constant (re)assignments. we may want to handle this more efficiently in the future');
    return;
  }

  ASSERT(indexOld !== indexNew, 'cant make an alias for itself', indexOld, indexNew, _origin);
  ASSERT(indexOld >= 0 && indexOld <= $domains.length, 'should be valid non-constant var index', indexOld, _origin);
  ASSERT(indexNew >= 0, 'should be valid var index', indexNew, _origin); // ASSERT($domains[indexOld], 'current domain shouldnt be empty', _origin);

  ASSERT(!indexOld || indexOld - 1 in $domains, 'dont create gaps...', indexOld);
  $aliases[indexOld] = indexNew;
  $domains[indexOld] = false; // Mark as aliased. while this isnt a change itself, it could lead to some dedupes

  if (!$valdist[indexNew] && $valdist[indexOld]) $valdist[indexNew] = $valdist[indexOld]; // This shouldnt happen for constants...
}

function $getAlias($aliases, index) {
  var alias = $aliases[index]; // TODO: is a trie faster compared to property misses?

  while (alias !== undefined) {
    TRACE_SILENT(' ($getAlias,', index, '=>', alias, ')');
    if (alias === index) THROW('alias is itself?', alias, index);
    index = alias;
    alias = $aliases[index];
  }

  return index;
}

function $getDomain($domains, $constants, $getAlias, varIndex, skipAliasCheck) {
  // ASSERT_LOG2('    - $getDomain', varIndex, skipAliasCheck, $constants[varIndex]);
  if (!skipAliasCheck) varIndex = $getAlias(varIndex);
  ASSERT(varIndex === $getAlias(varIndex), 'should only skip alias check when already certain the index is de-aliased', skipAliasCheck, varIndex, $getAlias(varIndex)); // Constant var indexes start at the end of the max

  var v = $constants[varIndex];

  if (v !== undefined) {
    ASSERT(SUB <= v && v <= SUP, 'only SUB SUP values are valid here');
    return domain_createValue(v);
  }

  return $domains[varIndex];
}

function _assertSetDomain($domains, $constants, $getAlias, varIndex, domain, skipAliasCheck, explicitlyAllowNewValuesForPseudoAlias) {
  // There's a bunch of stuff to assert. this function should not be called without ASSERT and should be eliminated as dead code by the minifier...
  // args check
  ASSERT(typeof varIndex === 'number' && varIndex >= 0 && varIndex <= 0xffff, 'valid varindex', varIndex);
  ASSERT_NORDOM(domain);
  ASSERT(skipAliasCheck === undefined || skipAliasCheck === true || skipAliasCheck === false, 'skipAliasCheck should be bool or undefined, was:', skipAliasCheck);
  var currentDomain = $getDomain($domains, $constants, $getAlias, varIndex, false);
  ASSERT(explicitlyAllowNewValuesForPseudoAlias || domain_intersection(currentDomain, domain) === domain, 'should not introduce values into the domain that did not exist before', domain__debug(currentDomain), '->', domain__debug(domain));
  ASSERT(domain, 'Should never be set to an empty domain, even with the explicitlyAllowNewValuesForPseudoAlias flag set');
  return true;
}

function $setDomain($domains, $constants, $aliases, $addAlias, $getAlias, varIndex, domain, skipAliasCheck, emptyHandled, explicitlyAllowNewValuesForPseudoAlias) {
  TRACE_SILENT('  $setDomain, index=', varIndex, ', from=', $constants[$getAlias(varIndex)] !== undefined ? 'constant ' + $constants[$getAlias(varIndex)] : domain__debug($domains[$getAlias(varIndex)]), ', to=', domain__debug(domain), ', skipAliasCheck=', skipAliasCheck, ', emptyHandled=', emptyHandled, ', explicitlyAllowNewValuesForPseudoAlias=', explicitlyAllowNewValuesForPseudoAlias);

  if (!domain) {
    if (emptyHandled) return; // Todo...

    THROW('Cannot set to empty domain');
  } // Handle elsewhere!


  ASSERT(_assertSetDomain($domains, $constants, $getAlias, varIndex, domain, skipAliasCheck, explicitlyAllowNewValuesForPseudoAlias));
  var value = domain_getValue(domain);
  if (value >= 0) return _$setToConstant($constants, $addAlias, varIndex, value);
  return _$setToDomain($domains, $constants, $aliases, $getAlias, varIndex, domain, skipAliasCheck);
}

function _$setToConstant($constants, $addAlias, varIndex, value) {
  // Check if this isnt already a constant.. this case should never happen
  // note: pseudo aliases should prevent de-aliasing when finalizing the aliased var
  if ($constants[varIndex] !== undefined) {
    // TOFIX: this needs to be handled better because a regular var may become mapped to a constant and if it becomes empty then this place cant deal/signal with that properly
    if ($constants[varIndex] === value) return;
    THROW('Cant update a constant (only to an empty domain, which should be handled differently)');
  } // Note: since the constant causes an alias anyways, we dont need to bother with alias lookup here
  // note: call site should assert that the varindex domain actually contained the value!


  var constantIndex = value2index($constants, value);
  $addAlias(varIndex, constantIndex, '$setDomain; because var is now constant ' + value);
}

function _$setToDomain($domains, $constants, $aliases, $getAlias, varIndex, domain, skipAliasCheck) {
  if (skipAliasCheck) {
    // Either index was already unaliased by call site or this is solution generating. unalias the var index just in case.
    $aliases[varIndex] = undefined;
  } else {
    varIndex = $getAlias(varIndex);
  }

  ASSERT(varIndex < $domains.length || $constants[varIndex] === domain, 'either the var is not a constant or it is being updated to itself');

  if (varIndex < $domains.length) {
    // TRACE_SILENT(' - now updating index', varIndex,'to', domain__debug(domain));
    $domains[varIndex] = domain; // } else {
    //  TRACE_SILENT(' - ignoring call, updating a constant to itself?', varIndex, '<', $domains.length, ', ', $constants[varIndex],' === ',domain);
  }
}

function value2index(constants, value) {
  // ASSERT_LOG2('value2index', value, '->', constants['v' + value]);
  ASSERT(value >= SUB && value <= SUP, 'value is OOB', value);
  var constantIndex = constants['v' + value];
  if (constantIndex >= 0) return constantIndex;
  constantIndex = MAX_VAR_COUNT - constants._count++;
  constants['v' + value] = constantIndex;
  constants[constantIndex] = value;
  return constantIndex;
}

function problem_create() {
  var anonCounter = 0;
  var varNames = [];
  var varTrie = trie_create(); // Name -> index (in varNames)

  var domains = [];
  var constants = {
    _count: 0
  };
  var aliases = {};
  var solveStack = [];
  var leafs = []; // Per-var distribution overrides. all vars default to the global distribution setting if set and otherwise naive

  var valdist = []; // 1:1 with varNames. contains json objects {valtype: 'name', ...}

  var addAlias = $addAlias.bind(undefined, domains, valdist, aliases, solveStack, constants);
  var getAlias = $getAlias.bind(undefined, aliases);
  var name2index = $name2index.bind(undefined, varTrie, getAlias);
  var targeted = [];
  var targetsFrozen = false; // False once a targets directive is parsed

  return {
    varTrie: varTrie,
    varNames: varNames,
    domains: domains,
    valdist: valdist,
    aliases: aliases,
    solveStack: solveStack,
    leafs: leafs,
    input: {
      // See dsl2ml
      varstrat: 'default',
      valstrat: 'default',
      dsl: ''
    },
    ml: undefined,
    // Uint8Array
    mapping: undefined,
    // Var index in (this) child to var index of parent
    addVar: $addVar.bind(undefined, varTrie, varNames, domains, valdist, constants, addAlias, function (_) {
      return ++anonCounter;
    }, targeted, function (_) {
      return targetsFrozen;
    }),
    getVar: name2index,
    // Deprecated
    name2index: name2index,
    addAlias: addAlias,
    getAlias: getAlias,
    getDomain: $getDomain.bind(undefined, domains, constants, getAlias),
    setDomain: $setDomain.bind(undefined, domains, constants, aliases, addAlias, getAlias),
    isConstant: function isConstant(index) {
      return constants[index] !== undefined;
    },
    freezeTargets: function freezeTargets(varNames) {
      if (targetsFrozen) THROW('Only one `targets` directive supported');
      targetsFrozen = true;
      targeted.fill(false);
      varNames.forEach(function (name) {
        return targeted[name2index(name, true)] = true;
      });
    },
    targeted: targeted // For each element in $domains; true if targeted, false if not targeted

  };
}

// Import dsl
/**
 * @param {string} dsl The input problem
 * @param {Function} solver The function to brute force the remainder of the problem after FDP reduces it, not called if already solved. Called with `solver(dsl, options)`.
 * @param {Object} fdpOptions
 * @property {boolean} [fdpOptions.singleCycle=false] Only do a single-nonloop minimization step before solving? Can be faster but sloppier.
 * @property {boolean} [fdpOptions.repeatUntilStable=true] Keep calling minimize/cutter per cycle until nothing changes?
 * @property {boolean} [fdpOptions.debugDsl=false] Enable debug output (adds lots of comments about vars)
 * @property {boolean} [fdpOptions.hashNames=true] Replace original varNames with `$<base36(index)>$` of their index in the output
 * @property {boolean} [fdpOptions.indexNames=false] Replace original varNames with `_<index>_` in the output
 * @property {boolean} [fdpOptions.groupedConstraints=true] When debugging only, add all constraints below a var decl where that var is used
 * @property {boolean} [fdpOptions.flattened=false] Solve all vars in the solution even if there are multiple open fdpOptions left
 * @property {boolean|Function} [fdpOptions.printDslBefore] Print the dsl after parsing it but before crunching it.
 * @property {boolean|Function} [fdpOptions.printDslAfter] Print the dsl after crunching it but before calling FD on it
 * @param {Object} solverOptions Passed on to the solver directly
 */

function solve(dsl, solver, fdpOptions, solverOptions) {
  if (fdpOptions === void 0) {
    fdpOptions = {};
  }

  if (solverOptions === void 0) {
    solverOptions = {
      log: 1,
      vars: 'all'
    };
  }

  ASSERT(typeof dsl === 'string');
  ASSERT(typeof fdpOptions !== 'function', 'confirming this isnt the old solver param'); // fdpOptions.hashNames = false;
  // fdpOptions.repeatUntilStable = true;
  // fdpOptions.debugDsl = false;
  // fdpOptions.singleCycle = true;
  // fdpOptions.indexNames = true;
  // fdpOptions.groupedConstraints = true;

  if (solverOptions.logger) setTerm(solverOptions.logger);
  var term = getTerm();
  term.log('<pre>');
  term.time('</pre>');

  var r = _preSolver(dsl, solver, fdpOptions, solverOptions);

  term.timeEnd('</pre>');
  return r;
}

function _preSolver(dsl, solver, options, solveOptions) {
  ASSERT(typeof dsl === 'string');
  ASSERT(typeof options !== 'function', 'making sure this isnt the old Solver param');
  var term = getTerm();
  term.log('<pre-solving>');
  term.time('</pre-solving total>');
  var _options$hashNames = options.hashNames,
      hashNames = _options$hashNames === void 0 ? true : _options$hashNames,
      _options$debugDsl = options.debugDsl,
      debugDsl = _options$debugDsl === void 0 ? false : _options$debugDsl,
      _options$indexNames = options.indexNames,
      indexNames = _options$indexNames === void 0 ? false : _options$indexNames,
      _options$groupedConst = options.groupedConstraints,
      groupedConstraints = _options$groupedConst === void 0 ? true : _options$groupedConst;
  if (options.hashNames === undefined) options.hashNames = hashNames;
  if (options.debugDsl === undefined) options.debugDsl = debugDsl;
  if (options.indexNames === undefined) options.indexNames = indexNames;
  if (options.groupedConstraints === undefined) options.groupedConstraints = groupedConstraints;
  var problem = problem_create();
  var varNames = problem.varNames,
      domains = problem.domains;
  TRACE(dsl.slice(0, 1000) + (dsl.length > 1000 ? ' ... <trimmed>' : '') + '\n');
  var state = crunch(dsl, problem, options);
  var bounty;
  var betweenDsl;

  if (state === $REJECTED) {
    TRACE('Skipping ml2dsl because problem rejected and bounty/ml2dsl dont handle empty domains well');
  } else {
    term.time('ml->dsl');
    bounty = bounty_collect(problem.ml, problem);
    betweenDsl = ml2dsl(problem.ml, problem, bounty, {
      debugDsl: false,
      hashNames: true
    }); // Use default generator settings for dsl to pass on to FD

    term.timeEnd('ml->dsl');
  }

  term.timeEnd('</pre-solving total>');
  if (state === $REJECTED) term.log('REJECTED'); // term.log(domains.map((d,i) => i+':'+problem.targeted[i]).join(', '));
  // confirm domains has no gaps...
  // term.log(problem.domains)
  // for (let i=0; i<domains.length; ++i) {
  //  ASSERT(i in domains, 'no gaps');
  //  ASSERT(domains[i] !== undefined, 'no pseudo gaps');
  // }
  // cutter cant reject, only reduce. may eliminate the last standing constraints.

  var solution;

  if (state === $SOLVED || state !== $REJECTED && !ml_hasConstraint(problem.ml)) {
    term.time('- generating early solution');
    solution = createSolution(problem, null, options);
    term.timeEnd('- generating early solution');
  }

  if (state !== $REJECTED && (betweenDsl && betweenDsl.length < 1000 || options.printDslAfter)) {
    var dslForLogging = ml2dsl(problem.ml, problem, bounty, options);
    var s = '\nResult dsl (debugDsl=' + debugDsl + ', hashNames=' + hashNames + ', indexNames=' + indexNames + '):\n' + dslForLogging;

    if (typeof options.printDslAfter === 'function') {
      options.printDslAfter(s);
    } else {
      term.log('#### <DSL> after crunching before FD');
      term.log(s);
      term.log('#### </DSL>');
    }
  }

  if (solution) {
    term.log('<solved without fdq>');
    return solution;
  }

  if (state === $REJECTED) {
    term.log('<rejected without fdq>');
    TRACE('problem rejected!');
    return 'rejected';
  }

  if (problem.input.varstrat === 'throw') {
    // The stats are for tests. dist will never even have this so this should be fine.
    // it's very difficult to ensure optimizations work properly otherwise
    if (process.env.NODE_ENV !== 'production') {
      ASSERT(false, "Forcing a choice with strat=throw; debug: " + varNames.length + " vars, " + ml_countConstraints(problem.ml) + " constraints, current domain state: " + domains.map(function (d, i) {
        return i + ':' + varNames[i] + ':' + domain__debug(d).replace(/[a-z()\[\]]/g, '');
      }).join(': ') + " (" + problem.leafs.length + " leafs) ops: " + ml_getOpList(problem.ml) + " #");
    }

    THROW('Forcing a choice with strat=throw');
  }

  term.log('\n\nSolving remaining problem through fdq now...');
  term.log('<FD>');
  term.time('</FD>');
  var fdSolution = solver(betweenDsl, solveOptions);
  term.timeEnd('</FD>');
  term.log('\n'); // Now merge the results from fdSolution to construct the final solution
  // we need to map the vars from the dsl back to the original names.
  // "our" vars will be constructed like `$<hash>$` where the hash simply
  // means "our" var index as base36. So all we need to do is remove the
  // dollar signs and parseInt as base 36. Ignore all other vars as they
  // are temporary vars generated by fdq. We should not see them
  // anymore once we support targeted vars.

  term.log('fd result:', typeof fdSolution === 'string' ? fdSolution : 'SOLVED');
  TRACE('fdSolution = ', fdSolution ? Object.keys(fdSolution).length > 100 ? '<supressed; too big>' : fdSolution : 'REJECT');

  if (fdSolution && typeof fdSolution !== 'string') {
    term.log('<solved after fdq>');

    if (Array.isArray(fdSolution)) {
      return fdSolution.map(function (sol) {
        return createSolution(problem, sol, options);
      });
    }

    return createSolution(problem, fdSolution, options);
  }

  term.log('<' + fdSolution + ' during fdq>');
  TRACE('problem rejected!');
  return 'rejected';
}

function crunch(dsl, problem, options) {
  if (options === void 0) {
    options = {};
  }

  var _options = options,
      _options$singleCycle = _options.singleCycle,
      singleCycle = _options$singleCycle === void 0 ? false : _options$singleCycle,
      _options$repeatUntilS = _options.repeatUntilStable,
      repeatUntilStable = _options$repeatUntilS === void 0 ? true : _options$repeatUntilS;
  var varNames = problem.varNames,
      domains = problem.domains,
      solveStack = problem.solveStack,
      $addVar = problem.$addVar,
      $getVar = problem.$getVar,
      $addAlias = problem.$addAlias,
      $getAlias = problem.$getAlias;
  var term = getTerm();
  term.time('- dsl->ml');
  dsl2ml(dsl, problem);
  var ml = problem.ml;
  term.timeEnd('- dsl->ml');
  term.log('Parsed dsl (' + dsl.length + ' bytes) into ml (' + ml.length + ' bytes)');

  if (options.printDslBefore) {
    var bounty = bounty_collect(problem.ml, problem);
    var predsl = ml2dsl(ml, problem, bounty, options);

    if (typeof options.printDslBefore === 'function') {
      options.printDslBefore(predsl);
    } else {
      term.log('#### <DSL> after parsing before crunching');
      term.log(predsl);
      term.log('#### </DSL>');
    }
  }

  var state;

  if (singleCycle) {
    // Only single cycle? usually most dramatic reduction. only runs a single loop of every step.
    term.time('- first minimizer cycle (single loop)');
    state = min_run(ml, problem, domains, varNames, true, !repeatUntilStable);
    term.timeEnd('- first minimizer cycle (single loop)');
    TRACE('First minimize pass result:', state);

    if (state !== $REJECTED) {
      term.time('- deduper cycle #');
      var deduperAddedAlias = deduper(ml, problem);
      term.timeEnd('- deduper cycle #');

      if (deduperAddedAlias >= 0) {
        term.time('- cutter cycle #');
        cutter(ml, problem, !repeatUntilStable);
        term.timeEnd('- cutter cycle #');
      }
    }
  } else {
    // Multiple cycles? more expensive, may not be worth the gains
    var runLoops = 0;
    term.time('- all run cycles');

    do {
      TRACE('run loop...');
      state = run_cycle(ml, $getVar, $addVar, domains, varNames, $addAlias, $getAlias, solveStack, runLoops++, problem);
    } while (state === $CHANGED);

    term.timeEnd('- all run cycles');
  }

  return state;
}

function run_cycle(ml, getVar, addVar, domains, vars, addAlias, getAlias, solveStack, runLoops, problem) {
  var term = getTerm();
  term.time('- run_cycle #' + runLoops);
  term.time('- minimizer cycle #' + runLoops);
  var state = min_run(ml, problem, domains, vars, runLoops === 0);
  term.timeEnd('- minimizer cycle #' + runLoops);
  if (state === $SOLVED) return state;
  if (state === $REJECTED) return state;
  term.time('- deduper cycle #' + runLoops);
  var deduperAddedAlias = deduper(ml, problem);
  term.timeEnd('- deduper cycle #' + runLoops);

  if (deduperAddedAlias < 0) {
    state = $REJECTED;
  } else {
    term.time('- cutter cycle #' + runLoops);
    var cutLoops = cutter(ml, problem, false);
    term.timeEnd('- cutter cycle #' + runLoops);
    if (cutLoops > 1 || deduperAddedAlias) state = $CHANGED;else if (cutLoops < 0) state = $REJECTED;else {
      ASSERT(state === $CHANGED || state === $STABLE, 'minimize state should be either stable or changed here');
    }
  }

  term.timeEnd('- run_cycle #' + runLoops);
  return state;
}

function createSolution(problem, fdSolution, options, max) {
  getTerm().time('createSolution()');
  var _options$flattened = options.flattened,
      flattened = _options$flattened === void 0 ? false : _options$flattened;
  var varNames = problem.varNames,
      domains = problem.domains,
      solveStack = problem.solveStack,
      getAlias = problem.getAlias,
      targeted = problem.targeted;
  var _getDomainWithoutFd = problem.getDomain;
  var _setDomainWithoutFd = problem.setDomain;

  function getDomainFromSolverOrLocal(index, skipAliasCheck) {
    if (!skipAliasCheck) index = getAlias(index);

    if (fdSolution) {
      var key = '$' + index.toString(36) + '$';
      var fdval = fdSolution[key];

      if (typeof fdval === 'number') {
        return domain_createValue(fdval);
      }

      if (fdval !== undefined) {
        ASSERT(fdval instanceof Array, 'expecting fdq to only create solutions as arrays or numbers', fdval);
        return domain_arrToSmallest(fdval);
      } // else the var was already solved by fd2 so just read from our local domains array

    }

    return _getDomainWithoutFd(index, true);
  }

  function setDomainInFdAndLocal(index, domain, skipAliasCheck, forPseudoAlias) {
    TRACE(' - solveStackSetDomain, index=', index, ', domain=', domain__debug(domain), ', skipAliasCheck=', skipAliasCheck, ', forPseudoAlias=', forPseudoAlias);
    ASSERT(domain, 'should not set an empty domain at this point');
    ASSERT(forPseudoAlias || domain_intersection(_getDomainWithoutFd(index), domain) === domain, 'should not introduce values into the domain that did not exist before unless for xnor pseudo-booly; current:', domain__debug(_getDomainWithoutFd(index)), ', updating to:', domain__debug(domain), 'varIndex:', index);
    if (!skipAliasCheck) index = getAlias(index);

    _setDomainWithoutFd(index, domain, true, false, forPseudoAlias); // Update the FD result AND the local data structure to reflect this new domain
    // the FD value rules when checking intersection with the new domain
    // (but we can just use the getter abstraction here and overwrite regardless)


    if (fdSolution) {
      var key = '$' + index.toString(36) + '$';

      if (fdSolution[key] !== undefined) {
        var v = domain_getValue(domain);
        if (v >= 0) fdSolution[key] = v;else fdSolution[key] = domain_toArr(domain);
      }
    }
  }

  function force(varIndex, pseudoDomain) {
    ASSERT(typeof varIndex === 'number' && varIndex >= 0 && varIndex <= 0xffff, 'valid var to solve', varIndex);
    var finalVarIndex = getAlias(varIndex);
    var domain = getDomainFromSolverOrLocal(finalVarIndex, true); // NOTE: this will take from fdSolution if it contains a value, otherwise from local domains

    ASSERT_NORDOM(domain);
    ASSERT(pseudoDomain === undefined || domain_intersection(pseudoDomain, domain) === pseudoDomain, 'pseudoDomain should not introduce new values');
    var v = domain_getValue(domain);

    if (v < 0) {
      if (pseudoDomain) {
        TRACE('   - force() using pseudo domain', domain__debug(pseudoDomain), 'instead of actual domain', domain__debug(domain));
        domain = pseudoDomain;
      }

      TRACE('   - forcing index', varIndex, '(final index=', finalVarIndex, ') to min(' + domain__debug(domain) + '):', domain_min(domain));
      var dist = problem.valdist[varIndex];

      if (dist) {
        ASSERT(typeof dist === 'object', 'dist is an object');
        ASSERT(typeof dist.valtype === 'string', 'dist object should have a name'); // TODO: rename valtype to "name"? or maybe keep it this way because easier to search for anyways. *shrug*

        switch (dist.valtype) {
          case 'list':
            ASSERT(Array.isArray(dist.list), 'lists should have a prio');
            dist.list.some(function (w) {
              return domain_containsValue(domain, w) && (v = w) >= 0;
            });
            if (v < 0) v = domain_min(domain); // None of the prioritized values still exist so just pick one

            break;

          case 'max':
            v = domain_max(domain);
            break;

          case 'min':
          case 'naive':
            v = domain_min(domain);
            break;

          case 'mid':
            v = domain_middleElement(domain);
            break;

          case 'markov':
          case 'minMaxCycle':
          case 'splitMax':
          case 'splitMin':
            THROW('implement me (var mod) [' + dist.valtype + ']');
            v = domain_min(domain);
            break;

          default:
            THROW('Unknown dist name: [' + dist.valtype + ']', dist);
        }
      } else {
        // Just an arbitrary choice then
        v = domain_min(domain);
      }

      ASSERT(domain_containsValue(domain, v), 'force() should not introduce new values');
      setDomainInFdAndLocal(varIndex, domain_createValue(v), true);
    }

    return v;
  }

  TRACE('\n# createSolution(), solveStack.length=', solveStack.length, ', using fdSolution?', !!fdSolution);
  TRACE(' - fdSolution:', domains.length < 50 ? INSPECT(fdSolution).replace(/\n/g, '') : '<big>');
  TRACE(' - domains:', domains.length < 50 ? domains.map(function (_, i) {
    return '{index=' + i + ',name=' + problem.varNames[i] + ',' + domain__debug(problem.getDomain(i)) + '}';
  }).join(', ') : '<big>');
  ASSERT(domains.length < 50 || !void TRACE('domains before; index, unaliased, aliased, fdSolution (if any):\n', domains.map(function (d, i) {
    return i + ': ' + domain__debug(d) + ', ' + domain__debug(_getDomainWithoutFd(i)) + ', ' + domain__debug(getDomainFromSolverOrLocal(i));
  })));

  function flushSolveStack() {
    TRACE('Flushing solve stack...', solveStack.length ? '' : ' and done! (solve stack was empty)');
    var rev = solveStack.reverse();

    for (var i = 0; i < rev.length; ++i) {
      var f = rev[i];
      TRACE('- solve stack entry', i);
      f(domains, force, getDomainFromSolverOrLocal, setDomainInFdAndLocal);
      TRACE(domains.length < 50 ? ' - domains now: ' + domains.map(function (_, i) {
        return '{index=' + i + ',name=' + problem.varNames[i] + ',' + domain__debug(problem.getDomain(i)) + '}';
      }).join(', ') : '');
    }

    ASSERT(domains.length < 50 || !void TRACE('domains after solve stack flush; index, unaliased, aliased, fdSolution (if any):\n', domains.map(function (d, i) {
      return i + ': ' + domain__debug(d) + ', ' + domain__debug(_getDomainWithoutFd(i)) + ', ' + domain__debug(getDomainFromSolverOrLocal(i));
    })));
  }

  flushSolveStack();
  ASSERT(!void domains.forEach(function (d, i) {
    return ASSERT(domains[i] === false ? getAlias(i) !== i : ASSERT_NORDOM(d), 'domains should be aliased or nordom at this point', 'index=' + i, ', alias=', getAlias(i), ', domain=' + domain__debug(d), domains);
  }));

  function flushValDists() {
    TRACE('\n# flushValDists: One last loop through all vars to force those with a valdist');

    for (var i = 0; i < domains.length; ++i) {
      if (flattened || problem.valdist[i]) {
        // Can ignore FD here (I think)
        _setDomainWithoutFd(i, domain_createValue(force(i)), true);
      } else {
        // TOFIX: make this more efficient... (cache the domain somehow)
        var domain = getDomainFromSolverOrLocal(i);
        var v = domain_getValue(domain);

        if (v >= 0) {
          // Can ignore FD here (I think)
          _setDomainWithoutFd(i, domain, true);
        }
      }
    }
  }

  flushValDists();
  TRACE('\n');
  ASSERT(domains.length < 50 || !void TRACE('domains after dist pops; index, unaliased, aliased, fdSolution (if any):\n', domains.map(function (d, i) {
    return i + ': ' + domain__debug(d) + ', ' + domain__debug(_getDomainWithoutFd(i)) + ', ' + domain__debug(getDomainFromSolverOrLocal(i));
  })));
  ASSERT(!void domains.forEach(function (d, i) {
    return ASSERT(d === false ? getAlias(i) !== i : flattened ? domain_getValue(d) >= 0 : ASSERT_NORDOM(d), 'domains should be aliased or nordom at this point', 'index=' + i, ', alias=', getAlias(i), 'domain=' + domain__debug(d), domains);
  }));

  function flushAliases() {
    TRACE(' - syncing aliases');

    for (var i = 0; i < domains.length; ++i) {
      var d = domains[i];

      if (d === false) {
        var a = getAlias(i);
        var v = force(a);
        TRACE('Forcing', i, 'and', a, 'to be equal because they are aliased, resulting value=', v); // Can ignore FD here (I think)

        _setDomainWithoutFd(i, domain_createValue(v), true);
      }
    }
  }

  flushAliases();
  ASSERT(domains.length < 50 || !void TRACE('domains after dealiasing; index, unaliased, aliased, fdSolution (if any):\n', domains.map(function (d, i) {
    return i + ': ' + domain__debug(d) + ', ' + domain__debug(_getDomainWithoutFd(i)) + ', ' + domain__debug(getDomainFromSolverOrLocal(i));
  })));

  function generateFinalSolution() {
    TRACE(' - generating regular FINAL solution', flattened);
    var solution = {};

    for (var index = 0; index < varNames.length; ++index) {
      if (targeted[index]) {
        var name = varNames[index];
        var d = getDomainFromSolverOrLocal(index);
        var v = domain_getValue(d);

        if (v >= 0) {
          d = v;
        } else if (flattened) {
          ASSERT(!problem.valdist[index], 'only vars without valdist may not be solved at this point');
          d = domain_min(d);
        } else {
          d = domain_toArr(d);
        }

        solution[name] = d;
      }
    }

    return solution;
  }

  var solution = generateFinalSolution();
  getTerm().timeEnd('createSolution()');
  TRACE(' -> createSolution results in:', domains.length > 100 ? '<supressed; too many vars (' + domains.length + ')>' : solution);
  return solution;
}

var fdp = {
  solve: solve
};

export default fdp;
