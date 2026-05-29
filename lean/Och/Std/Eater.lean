import Och.Macro
import Och.Eval
import Och.API

/-!
# Eater: a simple fix example

Demonstrates concrete evaluation of a recursive term.

```
bool_  = λt. λf. ⊤
true_  = λt. λf. t
false_ = λt. λf. f
eater  = fix e. λ(b : bool_). b ⊤ e
```

`eater` consumes `false_` arguments one at a time, unrolling via [E-Fix]
at each step. When it receives `true_`, it returns ⊤ and stops accepting
arguments. Applying further arguments after `true_` is stuck: ⊤ is not
a lambda.
-/

namespace Eater

def bool_  := och{ λt. λf. Type }
def true_  := och{ λt. λf. t }
def false_ := och{ λt. λf. f }
def eater  := och{ fix e. λb:bool_. b Type e }

section Tests

-- eater is well-formed
example : (Och.check och{ eater false_  }).isOk := by native_decide
example : (Och.check och{ eater false_ }).isOk := by native_decide
example : (Och.check och{ eater false_ true_ }).isOk := by native_decide
example : (Och.check och{ eater true_ false_ }).isError := by native_decide

-- eater applied to false_ evaluates to the unrolled form (a lambda),
-- ready to accept another argument.
example : (concEval 50 (och{ eater false_ })).isOk := by native_decide
example : concEval 50 (och{ eater false_ }) = concEval 50 (och{ eater }) := by native_decide

-- eater false_ false_ false_ true_ evaluates to Type (⊤)
example : concEval 100 (och{ eater false_ false_ false_ true_ }) = .ok .type := by native_decide

-- eater true_ evaluates to Type (⊤)
example : concEval 50 (och{ eater true_ }) = .ok .type := by native_decide

-- eater false_ true_ evaluates to Type (⊤)
example : concEval 50 (och{ eater false_ true_ }) = .ok .type := by native_decide

-- eater false_ true_ false_ is stuck: true_ returns ⊤, and ⊤ is not
-- a lambda, so applying false_ to it fails.
example : (concEval 50 (och{ eater false_ true_ false_ })).isError := by native_decide

end Tests

end Eater
