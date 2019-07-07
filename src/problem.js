import {
  ASSERT,
  ASSERT_NORDOM,
  TRACE,
  TRACE_SILENT,
  SUB,
  SUP,
  domain__debug,
  domain_arrToSmallest,
  domain_createRange,
  domain_createValue,
  domain_getValue,
  domain_intersection,
  THROW,
  trie_add,
  trie_create,
  trie_get
} from 'fdlib';

import {
  ML_JMP,
  ML_NOOP,
  ML_NOOP2,
  ML_NOOP3,
  ML_NOOP4,
  ML_STOP,
  ml_enc8,
  ml_compileJumpSafe,
  ml_validateSkeleton,
  ml_walk,
} from './ml';

const MAX_VAR_COUNT = 0xffff; // 16bit

function $addVar(
  $varTrie,
  $vars,
  $domains,
  $valdist,
  $constants,
  $addAlias,
  $getAnonCounter,
  $targeted,
  $targetsFrozen,
  name,
  domain,
  modifier,
  returnName,
  returnIndex,
  _throw
) {
  TRACE(
    'addVar',
    name,
    domain,
    modifier,
    returnName ? '(return name)' : '',
    returnIndex ? '(return index)' : ''
  );
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

  let newIndex;

  const v = domain_getValue(domain);
  if (typeof name === 'string' || v < 0 || returnName) {
    const wasAnon = name === undefined;
    if (wasAnon) {
      name = '__' + $getAnonCounter();
      TRACE(' - Adding anonymous var for dom=', domain, '->', name);
    } else if (
      name[0] === '_' &&
      name[1] === '_' &&
      name === '__' + parseInt(name.slice(2), 10)
    ) {
      THROW(
        'Dont use `__xxx` as var names, that structure is preserved for internal/anonymous var names'
      );
    }

    newIndex = $vars.length;

    const prev = trie_add($varTrie, name, newIndex);
    if (prev >= 0) {
      if (_throw)
        _throw(
          'CONSTRAINT_VARS_SHOULD_BE_DECLARED; Dont declare a var [' +
            name +
            '] after using it',
          name,
          prev
        );
      THROW(
        'CONSTRAINT_VARS_SHOULD_BE_DECLARED; Dont declare a var [' +
          name +
          '] after using it',
        name,
        prev
      );
    }

    $vars.push(name);
    $domains.push(domain);
    $targeted[newIndex] = wasAnon ? false : !$targetsFrozen(); // Note: cannot override frozen values since all names must already be declared when using `@custom targets`
  }

  // Note: if the name is string but domain is constant, we must add the name here as well and immediately alias it to a constant
  if (v >= 0 && !returnName) {
    // TODO: we'll phase out the second condition here soon, but right now constants can still end up as regular vars
    // constants are compiled slightly differently
    const constIndex = value2index($constants, v);
    // Actual var names must be registered so they can be looked up, then immediately alias them to a constant
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
  }

  // Deal with explicitly requested return values...
  if (returnIndex) return newIndex;
  if (returnName) return name;
}

function $name2index($varTrie, $getAlias, name, skipAliasCheck, scanOnly) {
  // ASSERT_LOG2('$name2index', name, skipAliasCheck);
  let varIndex = trie_get($varTrie, name);
  if (!scanOnly && varIndex < 0)
    THROW(
      'cant use this on constants or vars that have not (yet) been declared',
      name,
      varIndex
    );
  if (!skipAliasCheck && varIndex >= 0) varIndex = $getAlias(varIndex);
  return varIndex;
}

function $addAlias(
  $domains,
  $valdist,
  $aliases,
  $solveStack,
  $constants,
  indexOld,
  indexNew,
  _origin
) {
  TRACE(
    ' - $addAlias' +
      (_origin ? ' (from ' + _origin + ')' : '') +
      ': Mapping index = ',
    indexOld,
    '(',
    domain__debug($domains[indexOld]),
    ') to index = ',
    indexNew,
    '(',
    indexNew >= $domains.length
      ? 'constant ' + $constants[indexNew]
      : domain__debug($domains[indexNew]),
    ')'
  );
  ASSERT(
    typeof indexOld === 'number',
    'old index should be a number',
    indexOld
  );
  ASSERT(
    typeof indexNew === 'number',
    'new index should be a number',
    indexNew
  );

  if ($aliases[indexOld] === indexNew) {
    TRACE(
      'ignore constant (re)assignments. we may want to handle this more efficiently in the future'
    );
    return;
  }

  ASSERT(
    indexOld !== indexNew,
    'cant make an alias for itself',
    indexOld,
    indexNew,
    _origin
  );
  ASSERT(
    indexOld >= 0 && indexOld <= $domains.length,
    'should be valid non-constant var index',
    indexOld,
    _origin
  );
  ASSERT(indexNew >= 0, 'should be valid var index', indexNew, _origin);
  // ASSERT($domains[indexOld], 'current domain shouldnt be empty', _origin);
  ASSERT(
    !indexOld || indexOld - 1 in $domains,
    'dont create gaps...',
    indexOld
  );

  $aliases[indexOld] = indexNew;
  $domains[indexOld] = false; // Mark as aliased. while this isnt a change itself, it could lead to some dedupes
  if (!$valdist[indexNew] && $valdist[indexOld])
    $valdist[indexNew] = $valdist[indexOld]; // This shouldnt happen for constants...
}

function $getAlias($aliases, index) {
  let alias = $aliases[index]; // TODO: is a trie faster compared to property misses?
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
  ASSERT(
    varIndex === $getAlias(varIndex),
    'should only skip alias check when already certain the index is de-aliased',
    skipAliasCheck,
    varIndex,
    $getAlias(varIndex)
  );

  // Constant var indexes start at the end of the max
  const v = $constants[varIndex];
  if (v !== undefined) {
    ASSERT(SUB <= v && v <= SUP, 'only SUB SUP values are valid here');
    return domain_createValue(v);
  }

  return $domains[varIndex];
}

function _assertSetDomain(
  $domains,
  $constants,
  $getAlias,
  varIndex,
  domain,
  skipAliasCheck,
  explicitlyAllowNewValuesForPseudoAlias
) {
  // There's a bunch of stuff to assert. this function should not be called without ASSERT and should be eliminated as dead code by the minifier...

  // args check
  ASSERT(
    typeof varIndex === 'number' && varIndex >= 0 && varIndex <= 0xffff,
    'valid varindex',
    varIndex
  );
  ASSERT_NORDOM(domain);
  ASSERT(
    skipAliasCheck === undefined ||
      skipAliasCheck === true ||
      skipAliasCheck === false,
    'skipAliasCheck should be bool or undefined, was:',
    skipAliasCheck
  );

  const currentDomain = $getDomain(
    $domains,
    $constants,
    $getAlias,
    varIndex,
    false
  );
  ASSERT(
    explicitlyAllowNewValuesForPseudoAlias ||
      domain_intersection(currentDomain, domain) === domain,
    'should not introduce values into the domain that did not exist before',
    domain__debug(currentDomain),
    '->',
    domain__debug(domain)
  );
  ASSERT(
    domain,
    'Should never be set to an empty domain, even with the explicitlyAllowNewValuesForPseudoAlias flag set'
  );

  return true;
}

function $setDomain(
  $domains,
  $constants,
  $aliases,
  $addAlias,
  $getAlias,
  varIndex,
  domain,
  skipAliasCheck,
  emptyHandled,
  explicitlyAllowNewValuesForPseudoAlias
) {
  TRACE_SILENT(
    '  $setDomain, index=',
    varIndex,
    ', from=',
    $constants[$getAlias(varIndex)] !== undefined
      ? 'constant ' + $constants[$getAlias(varIndex)]
      : domain__debug($domains[$getAlias(varIndex)]),
    ', to=',
    domain__debug(domain),
    ', skipAliasCheck=',
    skipAliasCheck,
    ', emptyHandled=',
    emptyHandled,
    ', explicitlyAllowNewValuesForPseudoAlias=',
    explicitlyAllowNewValuesForPseudoAlias
  );
  if (!domain) {
    if (emptyHandled) return; // Todo...
    THROW('Cannot set to empty domain');
  } // Handle elsewhere!

  ASSERT(
    _assertSetDomain(
      $domains,
      $constants,
      $getAlias,
      varIndex,
      domain,
      skipAliasCheck,
      explicitlyAllowNewValuesForPseudoAlias
    )
  );

  const value = domain_getValue(domain);
  if (value >= 0)
    return _$setToConstant($constants, $addAlias, varIndex, value);
  return _$setToDomain(
    $domains,
    $constants,
    $aliases,
    $getAlias,
    varIndex,
    domain,
    skipAliasCheck
  );
}

function _$setToConstant($constants, $addAlias, varIndex, value) {
  // Check if this isnt already a constant.. this case should never happen
  // note: pseudo aliases should prevent de-aliasing when finalizing the aliased var
  if ($constants[varIndex] !== undefined) {
    // TOFIX: this needs to be handled better because a regular var may become mapped to a constant and if it becomes empty then this place cant deal/signal with that properly
    if ($constants[varIndex] === value) return;
    THROW(
      'Cant update a constant (only to an empty domain, which should be handled differently)'
    );
  }

  // Note: since the constant causes an alias anyways, we dont need to bother with alias lookup here
  // note: call site should assert that the varindex domain actually contained the value!
  const constantIndex = value2index($constants, value);
  $addAlias(
    varIndex,
    constantIndex,
    '$setDomain; because var is now constant ' + value
  );
}

function _$setToDomain(
  $domains,
  $constants,
  $aliases,
  $getAlias,
  varIndex,
  domain,
  skipAliasCheck
) {
  if (skipAliasCheck) {
    // Either index was already unaliased by call site or this is solution generating. unalias the var index just in case.
    $aliases[varIndex] = undefined;
  } else {
    varIndex = $getAlias(varIndex);
  }

  ASSERT(
    varIndex < $domains.length || $constants[varIndex] === domain,
    'either the var is not a constant or it is being updated to itself'
  );
  if (varIndex < $domains.length) {
    // TRACE_SILENT(' - now updating index', varIndex,'to', domain__debug(domain));
    $domains[varIndex] = domain;
    // } else {
    //  TRACE_SILENT(' - ignoring call, updating a constant to itself?', varIndex, '<', $domains.length, ', ', $constants[varIndex],' === ',domain);
  }
}

function value2index(constants, value) {
  // ASSERT_LOG2('value2index', value, '->', constants['v' + value]);
  ASSERT(value >= SUB && value <= SUP, 'value is OOB', value);

  let constantIndex = constants['v' + value];
  if (constantIndex >= 0) return constantIndex;

  constantIndex = MAX_VAR_COUNT - constants._count++;
  constants['v' + value] = constantIndex;
  constants[constantIndex] = value;

  return constantIndex;
}

function problem_create() {
  let anonCounter = 0;
  const varNames = [];
  const varTrie = trie_create(); // Name -> index (in varNames)
  const domains = [];
  const constants = { _count: 0 };
  const aliases = {};
  const solveStack = [];
  const leafs = [];

  // Per-var distribution overrides. all vars default to the global distribution setting if set and otherwise naive
  const valdist = []; // 1:1 with varNames. contains json objects {valtype: 'name', ...}

  const addAlias = $addAlias.bind(
    undefined,
    domains,
    valdist,
    aliases,
    solveStack,
    constants
  );
  const getAlias = $getAlias.bind(undefined, aliases);
  const name2index = $name2index.bind(undefined, varTrie, getAlias);

  const targeted = [];
  let targetsFrozen = false; // False once a targets directive is parsed

  return {
    varTrie,
    varNames,
    domains,
    valdist,
    aliases,
    solveStack,
    leafs,

    input: {
      // See dsl2ml
      varstrat: 'default',
      valstrat: 'default',
      dsl: '',
    },
    ml: undefined, // Uint8Array
    mapping: undefined, // Var index in (this) child to var index of parent

    addVar: $addVar.bind(
      undefined,
      varTrie,
      varNames,
      domains,
      valdist,
      constants,
      addAlias,
      _ => ++anonCounter,
      targeted,
      _ => targetsFrozen
    ),
    getVar: name2index, // Deprecated
    name2index,
    addAlias,
    getAlias,
    getDomain: $getDomain.bind(undefined, domains, constants, getAlias),
    setDomain: $setDomain.bind(
      undefined,
      domains,
      constants,
      aliases,
      addAlias,
      getAlias
    ),
    isConstant: index => constants[index] !== undefined,
    freezeTargets: varNames => {
      if (targetsFrozen) THROW('Only one `targets` directive supported');
      targetsFrozen = true;
      targeted.fill(false);
      varNames.forEach(name => (targeted[name2index(name, true)] = true));
    },

    targeted, // For each element in $domains; true if targeted, false if not targeted
  };
}

function problem_from(parentProblem) {
  TRACE(
    ' - problem_from(): sweeping parent and generating clean child problem'
  );
  const childProblem = problem_create(parentProblem._dsl);

  const parentMl = parentProblem.ml;
  childProblem.mapping = new Array(parentProblem.varNames.length);
  const len = parentMl.length;
  const childMl = new Uint8Array(len); // Worst case there's a lot of empty space to recycle
  // childMl.fill(0); // note: we shouldnt need to do this. everything but the left-over space is copied over directly. the left-over space is compiled as a full jump which should ignore the remaining contents of the buffer. it may only be a little confusing to debug if you expect that space to be "empty"
  childProblem.ml = childMl;

  let childOffset = 0;
  let lastJumpSize = 0;
  let lastJumpOffset = 0;
  let stopOffset = 0;
  ml_walk(parentMl, 0, (ml, offset, op, sizeof) => {
    switch (op) {
      case ML_JMP:
      case ML_NOOP:
      case ML_NOOP2:
      case ML_NOOP3:
      case ML_NOOP4:
        lastJumpOffset = offset;
        lastJumpSize = sizeof;
        return; // Eliminate these
      case ML_STOP:
        stopOffset = offset;
    }

    // Copy the bytes to the new problem ml
    // TODO: consolidate consecutive copies (probably faster to do one long copy than 10 short ones?)
    ml.copy(childMl, childOffset, offset, offset + sizeof);
    childOffset += sizeof;
  });
  TRACE(
    'ML len:',
    len,
    'parent content len:',
    stopOffset - lastJumpSize === lastJumpOffset
      ? lastJumpOffset + 1
      : stopOffset,
    ', child content len:',
    childOffset
  );
  ASSERT(
    childMl[childOffset - 1] === ML_STOP,
    'expecting last copied op to be a STOP',
    childOffset,
    childMl[childOffset - 1],
    childMl
  );
  if (childOffset < len) {
    TRACE(
      ' - there are',
      len - childOffset - 1,
      'available bytes left, compiling a jump and moving the STOP back'
    );
    ml_compileJumpSafe(childMl, childOffset - 1, len - childOffset);
    ml_enc8(childMl, len - 1, ML_STOP);
  }

  TRACE('PML:', parentMl);
  TRACE('CML:', childMl);
  ASSERT(ml_validateSkeleton(childMl, 'after streaming to a child ml'));

  return childProblem;
}

export { problem_create, problem_from };
