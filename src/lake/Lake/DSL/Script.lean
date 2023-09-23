/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Config.Package
import Lake.DSL.Attributes
import Lake.DSL.DeclUtil

namespace Lake.DSL
open Lean Parser Command

syntax scriptDeclSpec :=
  ident (ppSpace simpleBinder)? (declValSimple <|> declValDo)

/--
Define a new Lake script for the package. Has two forms:

```lean
script «script-name» (args) do /- ... -/
script «script-name» (args) := ...
```
-/
scoped syntax (name := scriptDecl)
(docComment)?  optional(Term.attributes) "script " scriptDeclSpec : command

@[macro scriptDecl]
def expandScriptDecl : Macro
| `($[$doc?]? $[$attrs?]? script $id:ident $[$args?]? do $seq $[$wds?]?) => do
  `($[$doc?]? $[$attrs?]? script $id:ident $[$args?]? := do $seq $[$wds?]?)
| `($[$doc?]? $[$attrs?]? script $id:ident $[$args?]? := $defn $[$wds?]?) => do
  let args ← expandOptSimpleBinder args?
  let attrs := #[← `(Term.attrInstance| «script»)] ++ expandAttrs attrs?
  `($[$doc?]? @[$attrs,*] def $id : ScriptFn := fun $args => $defn $[$wds?]?)
| stx => Macro.throwErrorAt stx "ill-formed script declaration"
