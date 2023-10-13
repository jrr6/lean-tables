import Lean
import Lean.Util.CollectLevelParams
import Lean.Elab.DeclUtil
import Lean.Elab.DefView
import Lean.Elab.Inductive
import Lean.Elab.Structure
import Lean.Elab.MutualDef
import Lean.Elab.DeclarationRange
namespace Lean.Elab.Command

open Meta

instance : ToString CtorView := ⟨λ (v : CtorView) =>
  "{ref: " ++ toString v.ref ++ "}\n" ++
  "{mods: " ++ toString v.modifiers ++ "}\n" ++
  "{decl: " ++ toString v.declName ++ "}\n" ++
  "{type?: " ++ toString v.type? ++ "}\n"
    ⟩

/-
leading_parser "inductive " >> declId >> optDeclSig >> optional ":=" >> many ctor
leading_parser atomic (group ("class " >> "inductive ")) >> declId >> optDeclSig >> optional ":=" >> many ctor >> optDeriving
-/
private def badInductiveSyntaxToView (modifiers : Modifiers) (decl : Syntax) : CommandElabM InductiveView := do
  checkValidInductiveModifier modifiers
  let (binders, type?) := expandOptDeclSig decl[2]
  let declId           := decl[1]
  let ⟨name, declName, levelNames⟩ ← expandDeclId declId modifiers
  addDeclarationRanges declName decl
  let ctors      ← decl[3].getArgs.mapM fun ctor => withRef ctor do
    -- def ctor := leading_parser " | " >> declModifiers >> ident >> optDeclSig
    let ctorModifiers ← elabModifiers ctor[1]
    if ctorModifiers.isPrivate && modifiers.isPrivate then
      throwError "invalid 'private' constructor in a 'private' inductive datatype"
    if ctorModifiers.isProtected && modifiers.isPrivate then
      throwError "invalid 'protected' constructor in a 'private' inductive datatype"
    checkValidCtorModifier ctorModifiers
    let ctorName := ctor.getIdAt 2
    let ctorName := declName ++ ctorName
    let ctorName ← withRef ctor[2] <| applyVisibility ctorModifiers.visibility ctorName
    let (binders, type?) := expandOptDeclSig ctor[3]
    addDocString' ctorName ctorModifiers.docString?
    addAuxDeclarationRanges ctorName ctor ctor[2]
    return { ref := ctor, modifiers := ctorModifiers, declName := ctorName, binders := binders, type? := type? : CtorView }
  let mut computedFields := #[]
  let mut classes := #[]
  if decl.getNumArgs == 5 then
    -- TODO: remove after stage0 update
    classes ← getOptDerivingClasses decl[4]
  else
    computedFields ← (decl[4].getOptional?.map (·[1].getArgs) |>.getD #[]).mapM fun cf => withRef cf do
      return { ref := cf, modifiers := cf[0], fieldId := cf[1].getId, type := ⟨cf[3]⟩, matchAlts := ⟨cf[4]⟩ }
    classes ← getOptDerivingClasses decl[6]
  return {
    ref             := decl
    shortDeclName   := name
    derivingClasses := classes
    declId, modifiers, declName, levelNames
    binders, type?, ctors
    computedFields
  }

private partial def elabHeaderAux (views : Array InductiveView) (i : Nat) (acc : Array ElabHeaderResult) : TermElabM (Array ElabHeaderResult) :=
  Term.withAutoBoundImplicitForbiddenPred (fun n => views.any (·.shortDeclName == n)) do
    if h : i < views.size then
      let view := views.get ⟨i, h⟩
      let acc ← Term.withAutoBoundImplicit <| Term.elabBinders view.binders.getArgs fun params => do
        match view.type? with
        | none         =>
          let u ← mkFreshLevelMVar
          let type := mkSort u
          Term.synthesizeSyntheticMVarsNoPostponing
          Term.addAutoBoundImplicits' params type fun params type => do
            return acc.push { lctx := (← getLCtx), localInsts := (← getLocalInstances), params, type, view }
        | some typeStx =>
          let (type, _) ← Term.withAutoBoundImplicit do
            let type ← Term.elabType typeStx
            unless (← isTypeFormerType type) do
              throwErrorAt typeStx "invalid inductive type, resultant type is not a sort"
            Term.synthesizeSyntheticMVarsNoPostponing
            let indices ← Term.addAutoBoundImplicits #[]
            return (← mkForallFVars indices type, indices.size)
          Term.addAutoBoundImplicits' params type fun params type => do
            trace[Elab.inductive] "header params: {params}, type: {type}"
            return acc.push { lctx := (← getLCtx), localInsts := (← getLocalInstances), params, type, view }
      elabHeaderAux views (i+1) acc
    else
      return acc

private def elabHeader (views : Array InductiveView) : TermElabM (Array ElabHeaderResult) := do
  let rs ← elabHeaderAux views 0 #[]
  -- if rs.size > 1 then
    -- checkUnsafe rs
    -- let numParams ← checkNumParams rs
    -- checkHeaders rs numParams 0 none
  return rs

private def mkTypeFor (r : ElabHeaderResult) : TermElabM Expr := do
  withLCtx r.lctx r.localInsts do
    mkForallFVars r.params r.type

private partial def withInductiveLocalDecls (rs : Array ElabHeaderResult) (x : Array Expr → Array Expr → TermElabM α) : TermElabM α := do
  let namesAndTypes ← rs.mapM fun r => do
    let type ← mkTypeFor r
    pure (r.view.declName, r.view.shortDeclName, type)
  let r0     := rs[0]!
  let params := r0.params
  withLCtx r0.lctx r0.localInsts <| withRef r0.view.ref do
    let rec loop (i : Nat) (indFVars : Array Expr) := do
      if h : i < namesAndTypes.size then
        let (declName, shortDeclName, type) := namesAndTypes.get ⟨i, h⟩
        Term.withAuxDecl shortDeclName type declName fun indFVar => loop (i+1) (indFVars.push indFVar)
      else
        x params indFVars
    loop 0 #[]

private def withExplicitToImplicit (xs : Array Expr) (k : TermElabM α) : TermElabM α := do
  let mut toImplicit := #[]
  for x in xs do
    if (← getFVarLocalDecl x).binderInfo.isExplicit then
      toImplicit := toImplicit.push (x.fvarId!, BinderInfo.implicit)
  withNewBinderInfos toImplicit k

private def isInductiveFamily (numParams : Nat) (indFVar : Expr) : TermElabM Bool := do
  let indFVarType ← inferType indFVar
  forallTelescopeReducing indFVarType fun xs _ =>
    return xs.size > numParams

private def getArrowBinderNames (type : Expr) : Array Name :=
  go type #[]
where
  go (type : Expr) (acc : Array Name) : Array Name :=
    match type with
    | .forallE n _ b _ => go b (acc.push n)
    | .mdata _ b       => go b acc
    | _ => acc

private def replaceArrowBinderNames (type : Expr) (newNames : Array Name) : Expr :=
  go type 0
where
  go (type : Expr) (i : Nat) : Expr :=
    if i < newNames.size then
      match type with
      | .forallE n d b bi =>
        if n.hasMacroScopes then
          mkForall newNames[i]! bi d (go b (i+1))
        else
          mkForall n bi d (go b (i+1))
      | _ => type
    else
      type

private def reorderCtorArgs (ctorType : Expr) : MetaM Expr := do
  forallTelescopeReducing ctorType fun as type => do
    /- `type` is of the form `C ...` where `C` is the inductive datatype being defined. -/
    let bs := type.getAppArgs
    let mut as  := as
    let mut bsPrefix := #[]
    for b in bs do
      unless b.isFVar && as.contains b do
        break
      let localDecl ← getFVarLocalDecl b
      if localDecl.binderInfo.isExplicit then
        break
      unless localDecl.userName.hasMacroScopes do
        break
      if (← localDeclDependsOnPred localDecl fun fvarId => as.any fun p => p.fvarId! == fvarId) then
        break
      bsPrefix := bsPrefix.push b
      as := as.erase b
    if bsPrefix.isEmpty then
      return ctorType
    else
      let r ← mkForallFVars (bsPrefix ++ as) type
      /- `r` already contains the resulting type.
         To be able to produce more better error messages, we copy the first `bsPrefix.size` binder names from `C` to `r`.
         This is important when some of contructor parameters were inferred using the auto-bound implicit feature.
         For example, in the following declaration.
         ```
          inductive Member : α → List α → Type u
            | head : Member a (a::as)
            | tail : Member a bs → Member a (b::bs)
         ```
         if we do not copy the binder names
         ```
         #check @Member.head
         ```
         produces `@Member.head : {x : Type u_1} → {a : x} → {as : List x} → Member a (a :: as)`
         which is correct, but a bit confusing. By copying the binder names, we obtain
         `@Member.head : {α : Type u_1} → {a : α} → {as : List α} → Member a (a :: as)`
       -/
      let C := type.getAppFn
      let binderNames := getArrowBinderNames (← instantiateMVars (← inferType C))
      return replaceArrowBinderNames r binderNames[:bsPrefix.size]

private def elabCtors (indFVars : Array Expr) (indFVar : Expr) (params : Array Expr) (r : ElabHeaderResult) : TermElabM (List Constructor) := withRef r.view.ref do
  let indFamily ← isInductiveFamily params.size indFVar
  r.view.ctors.toList.mapM fun ctorView =>
    Term.withAutoBoundImplicit <| Term.elabBinders ctorView.binders.getArgs fun ctorParams =>
      withRef ctorView.ref do
        let rec elabCtorType (k : Expr → TermElabM Constructor) : TermElabM Constructor := do
          match ctorView.type? with
          | none          =>
            if indFamily then
              throwError "constructor resulting type must be specified in inductive family declaration"
            k <| mkAppN indFVar params
          | some ctorType =>
            let type ← Term.elabType ctorType
            trace[Elab.inductive] "elabType {ctorView.declName} : {type} "
            Term.synthesizeSyntheticMVars (mayPostpone := true)
            let type ← instantiateMVars type
            let type ← checkParamOccs type
            forallTelescopeReducing type fun _ resultingType => do
              unless resultingType.getAppFn == indFVar do
                throwError "unexpected constructor resulting type{indentExpr resultingType}"
              unless (← isType resultingType) do
                throwError "unexpected constructor resulting type, type expected{indentExpr resultingType}"
            k type
        elabCtorType fun type => do
          Term.synthesizeSyntheticMVarsNoPostponing
          let ctorParams ← Term.addAutoBoundImplicits ctorParams
          let except (mvarId : MVarId) := ctorParams.any fun ctorParam => ctorParam.isMVar && ctorParam.mvarId! == mvarId
          /-
            We convert metavariables in the resulting type info extra parameters. Otherwise, we would not be able to elaborate
            declarations such as
            ```
            inductive Palindrome : List α → Prop where
              | nil      : Palindrome [] -- We would get an error here saying "failed to synthesize implicit argument" at `@List.nil ?m`
              | single   : (a : α) → Palindrome [a]
              | sandwich : (a : α) → Palindrome as → Palindrome ([a] ++ as ++ [a])
            ```
            We used to also collect unassigned metavariables on `ctorParams`, but it produced counterintuitive behavior.
            For example, the following declaration used to be accepted.
            ```
            inductive Foo
            | bar (x)

            #check Foo.bar
            -- @Foo.bar : {x : Sort u_1} → x → Foo
            ```
            which is also inconsistent with the behavior of auto implicits in definitions. For example, the following example was never accepted.
            ```
            def bar (x) := 1
            ```
          -/
          let extraCtorParams ← Term.collectUnassignedMVars (← instantiateMVars type) #[] except
          trace[Elab.inductive] "extraCtorParams: {extraCtorParams}"
          /- We must abstract `extraCtorParams` and `ctorParams` simultaneously to make
             sure we do not create auxiliary metavariables. -/
          let type  ← mkForallFVars (extraCtorParams ++ ctorParams) type
          let type ← reorderCtorArgs type
          let type ← mkForallFVars params type
          trace[Elab.inductive] "{ctorView.declName} : {type}"
          return { name := ctorView.declName, type }
where
  checkParamOccs (ctorType : Expr) : MetaM Expr :=
    let visit (e : Expr) : MetaM TransformStep := do
      let f := e.getAppFn
      if indFVars.contains f then
        let mut args := e.getAppArgs
        unless args.size ≥ params.size do
          throwError "unexpected inductive type occurrence{indentExpr e}"
        for i in [:params.size] do
          let param := params[i]!
          let arg := args[i]!
          unless (← isDefEq param arg) do
            throwError "inductive datatype parameter mismatch{indentExpr arg}\nexpected{indentExpr param}"
          args := args.set! i param
        return TransformStep.done (mkAppN f args)
      else
        return TransformStep.visit e
    transform ctorType (pre := visit)

private def getArity (indType : InductiveType) : MetaM Nat :=
  forallTelescopeReducing indType.type fun xs _ => return xs.size
private def resetMaskAt (mask : Array Bool) (i : Nat) : Array Bool :=
  if h : i < mask.size then
    mask.set ⟨i, h⟩ false
  else
    mask
private def computeFixedIndexBitMask (numParams : Nat) (indType : InductiveType) (indFVars : Array Expr) : MetaM (Array Bool) := do
  let arity ← getArity indType
  if arity ≤ numParams then
    return mkArray arity false
  else
    let maskRef ← IO.mkRef (mkArray numParams false ++ mkArray (arity - numParams) true)
    let rec go (ctors : List Constructor) : MetaM (Array Bool) := do
      match ctors with
      | [] => maskRef.get
      | ctor :: ctors =>
        forallTelescopeReducing ctor.type fun xs type => do
          let typeArgs := type.getAppArgs
          for i in [numParams:arity] do
            unless i < xs.size && xs[i]! == typeArgs[i]! do -- Remark: if we want to allow arguments to be rearranged, this test should be xs.contains typeArgs[i]
              maskRef.modify fun mask => mask.set! i false
          for x in xs[numParams:] do
            let xType ← inferType x
            xType.forEach fun e => do
              if indFVars.any (fun indFVar => e.getAppFn == indFVar) && e.getAppNumArgs > numParams then
                let eArgs := e.getAppArgs
                for i in [numParams:eArgs.size] do
                  if i >= typeArgs.size then
                    maskRef.modify (resetMaskAt · i)
                  else
                    unless eArgs[i]! == typeArgs[i]! do
                      maskRef.modify (resetMaskAt · i)
        go ctors
    go indType.ctors

private def isDomainDefEq (arrowType : Expr) (type : Expr) : MetaM Bool := do
  if !arrowType.isForall then
    return false
  else
    /-
      We used to use `withNewMCtxDepth` to make sure we do not assign universe metavariables,
      but it was not satisfactory. For example, in declarations such as
      ```
      inductive Eq : α → α → Prop where
      | refl (a : α) : Eq a a
      ```
      We want the first two indices to be promoted to parameters, and this will only
      happen if we can assign universe metavariables.
    -/
    isDefEq arrowType.bindingDomain! type

private partial def fixedIndicesToParams (numParams : Nat) (indTypes : Array InductiveType) (indFVars : Array Expr) : MetaM Nat := do
  let masks ← indTypes.mapM (computeFixedIndexBitMask numParams · indFVars)
  if masks.all fun mask => !mask.contains true then
    return numParams
  trace[Elab.inductive] "masks: {masks}"
  -- We process just a non-fixed prefix of the indices for now. Reason: we don't want to change the order.
  -- TODO: extend it in the future. For example, it should be reasonable to change
  -- the order of indices generated by the auto implicit feature.
  let mask := masks[0]!
  forallBoundedTelescope indTypes[0]!.type numParams fun params type => do
    let otherTypes ← indTypes[1:].toArray.mapM fun indType => do whnfD (← instantiateForall indType.type params)
    let ctorTypes ← indTypes.toList.mapM fun indType => indType.ctors.mapM fun ctor => do whnfD (← instantiateForall ctor.type params)
    let typesToCheck := otherTypes.toList ++ ctorTypes.join
    let rec go (i : Nat) (type : Expr) (typesToCheck : List Expr) : MetaM Nat := do
      if i < mask.size then
        if !masks.all fun mask => i < mask.size && mask[i]! then
           return i
        if !type.isForall then
          return i
        let paramType := type.bindingDomain!
        if !(← typesToCheck.allM fun type => isDomainDefEq type paramType) then
          trace[Elab.inductive] "domain not def eq: {i}, {type} =?= {paramType}"
          return i
        withLocalDeclD `a paramType fun paramNew => do
          let typesToCheck ← typesToCheck.mapM fun type => whnfD (type.bindingBody!.instantiate1 paramNew)
          go (i+1) (type.bindingBody!.instantiate1 paramNew) typesToCheck
      else
        return i
    go numParams type typesToCheck

private def getResultingUniverse : List InductiveType → TermElabM Level
  | []           => throwError "unexpected empty inductive declaration"
  | indType :: _ => forallTelescopeReducing indType.type fun _ r => do
    let r ← whnfD r
    match r with
    | Expr.sort u => return u
    | _           => throwError "unexpected inductive type resulting type{indentExpr r}"

private def collectUsed (indTypes : List InductiveType) : StateRefT CollectFVars.State MetaM Unit := do
  indTypes.forM fun indType => do
    indType.type.collectFVars
    indType.ctors.forM fun ctor =>
      ctor.type.collectFVars

private def removeUnused (vars : Array Expr) (indTypes : List InductiveType) : TermElabM (LocalContext × LocalInstances × Array Expr) := do
  let (_, used) ← (collectUsed indTypes).run {}
  Meta.removeUnused vars used

private def withUsed {α} (vars : Array Expr) (indTypes : List InductiveType) (k : Array Expr → TermElabM α) : TermElabM α := do
  let (lctx, localInsts, vars) ← removeUnused vars indTypes
  withLCtx lctx localInsts <| k vars

private def updateParams (vars : Array Expr) (indTypes : List InductiveType) : TermElabM (List InductiveType) :=
  indTypes.mapM fun indType => do
    let type ← mkForallFVars vars indType.type
    let ctors ← indType.ctors.mapM fun ctor => do
      let ctorType ← withExplicitToImplicit vars (mkForallFVars vars ctor.type)
      return { ctor with type := ctorType }
    return { indType with type, ctors }

private partial def collectUniverses (views : Array InductiveView) (r : Level) (rOffset : Nat) (numParams : Nat) (indTypes : List InductiveType) : TermElabM (Array Level) := do
  let (_, us) ← go |>.run #[]
  return us
where
  go : StateRefT (Array Level) TermElabM Unit :=
    indTypes.forM fun indType => indType.ctors.forM fun ctor =>
      withCtorRef views ctor.name do
        forallTelescopeReducing ctor.type fun ctorParams _ =>
          for ctorParam in ctorParams[numParams:] do
            accLevelAtCtor ctor ctorParam r rOffset

private def updateResultingUniverse (views : Array InductiveView) (numParams : Nat) (indTypes : List InductiveType) : TermElabM (List InductiveType) := do
  let r ← getResultingUniverse indTypes
  let rOffset : Nat   := r.getOffset
  let r       : Level := r.getLevelOffset
  unless r.isMVar do
    throwError "failed to compute resulting universe level of inductive datatype, provide universe explicitly: {r}"
  let us ← collectUniverses views r rOffset numParams indTypes
  trace[Elab.inductive] "updateResultingUniverse us: {us}, r: {r}, rOffset: {rOffset}"
  let rNew := mkResultUniverse us rOffset
  assignLevelMVar r.mvarId! rNew
  indTypes.mapM fun indType => do
    let type ← instantiateMVars indType.type
    let ctors ← indType.ctors.mapM fun ctor => return { ctor with type := (← instantiateMVars ctor.type) }
    return { indType with type, ctors }

private def levelMVarToParam (indTypes : List InductiveType) (univToInfer? : Option LMVarId) : TermElabM (List InductiveType) :=
  go |>.run' 1
where
  levelMVarToParam' (type : Expr) : StateRefT Nat TermElabM Expr := do
    Term.levelMVarToParam' type (except := fun mvarId => univToInfer? == some mvarId)

  go : StateRefT Nat TermElabM (List InductiveType) := do
    indTypes.mapM fun indType => do
      let type  ← levelMVarToParam' indType.type
      let ctors ← indType.ctors.mapM fun ctor => do
        let ctorType ← levelMVarToParam' ctor.type
        return { ctor with type := ctorType }
      return { indType with ctors, type }

private def collectLevelParamsInInductive (indTypes : List InductiveType) : Array Name := Id.run do
  let mut usedParams : CollectLevelParams.State := {}
  for indType in indTypes do
    usedParams := collectLevelParams usedParams indType.type
    for ctor in indType.ctors do
      usedParams := collectLevelParams usedParams ctor.type
  return usedParams.params

private def mkIndFVar2Const (views : Array InductiveView) (indFVars : Array Expr) (levelNames : List Name) : ExprMap Expr := Id.run do
  let levelParams := levelNames.map mkLevelParam;
  let mut m : ExprMap Expr := {}
  for i in [:views.size] do
    let view    := views[i]!
    let indFVar := indFVars[i]!
    m := m.insert indFVar (mkConst view.declName levelParams)
  return m

private def replaceIndFVarsWithConsts (views : Array InductiveView) (indFVars : Array Expr) (levelNames : List Name)
    (numVars : Nat) (numParams : Nat) (indTypes : List InductiveType) : TermElabM (List InductiveType) :=
  let indFVar2Const := mkIndFVar2Const views indFVars levelNames
  indTypes.mapM fun indType => do
    let ctors ← indType.ctors.mapM fun ctor => do
      let type ← forallBoundedTelescope ctor.type numParams fun params type => do
        let type := type.replace fun e =>
          if !e.isFVar then
            none
          else match indFVar2Const.find? e with
            | none   => none
            | some c => mkAppN c (params.extract 0 numVars)
        instantiateMVars (← mkForallFVars params type)
      return { ctor with type }
    return { indType with ctors }

private def mkAuxConstructions (views : Array InductiveView) : TermElabM Unit := do
  let env ← getEnv
  let hasEq   := env.contains ``Eq
  let hasHEq  := env.contains ``HEq
  let hasUnit := env.contains ``PUnit
  let hasProd := env.contains ``Prod
  for view in views do
    let n := view.declName
    mkRecOn n
    if hasUnit then mkCasesOn n
    if hasUnit && hasEq && hasHEq then mkNoConfusion n
    if hasUnit && hasProd then mkBelow n
    if hasUnit && hasProd then mkIBelow n
  for view in views do
    let n := view.declName;
    if hasUnit && hasProd then mkBRecOn n
    if hasUnit && hasProd then mkBInductionOn n

def addDecl [Monad m] [MonadEnv m] [MonadError m] [MonadOptions m] [MonadLog m] [AddMessageContext m] (decl : Declaration) : m Unit := do
  if !(← MonadLog.hasErrors) && decl.hasSorry then
    logWarning "declaration uses 'sorry'"
  match (← getEnv).addDecl decl with
  | Except.ok    env => setEnv env
  | Except.error ex  => throwKernelException ex

private def mkInductiveDecl (vars : Array Expr) (views : Array InductiveView) : TermElabM Unit := Term.withoutSavingRecAppSyntax do
  let view0 := views[0]!
  let scopeLevelNames ← Term.getLevelNames
  -- checkLevelNames views
  let allUserLevelNames := view0.levelNames
  let isUnsafe          := view0.modifiers.isUnsafe
  withRef view0.ref <| Term.withLevelNames allUserLevelNames do
    let rs ← elabHeader views
    withInductiveLocalDecls rs fun params indFVars => do
      trace[Elab.inductive] "indFVars: {indFVars}"
      let mut indTypesArray : Array InductiveType := #[]
      for i in [:views.size] do
        let indFVar := indFVars[i]!
        Term.addLocalVarInfo views[i]!.declId indFVar
        let r       := rs[i]!
        let type  ← mkForallFVars params r.type
        let ctors ← withExplicitToImplicit params (elabCtors indFVars indFVar params r)
        indTypesArray := indTypesArray.push { name := r.view.declName, type, ctors }
      Term.synthesizeSyntheticMVarsNoPostponing
      let numExplicitParams ← fixedIndicesToParams params.size indTypesArray indFVars
      trace[Elab.inductive] "numExplicitParams: {numExplicitParams}"
      let indTypes := indTypesArray.toList
      let u ← getResultingUniverse indTypes
      let univToInfer? ← shouldInferResultUniverse u
      withUsed vars indTypes fun vars => do
        let numVars   := vars.size
        let numParams := numVars + numExplicitParams
        let indTypes ← updateParams vars indTypes
        let indTypes ← if let some univToInfer := univToInfer? then
          updateResultingUniverse views numParams (← levelMVarToParam indTypes univToInfer)
        else
          -- checkResultingUniverses views numParams indTypes
          levelMVarToParam indTypes none
        let usedLevelNames := collectLevelParamsInInductive indTypes
        match sortDeclLevelParams scopeLevelNames allUserLevelNames usedLevelNames with
        | .error msg      => throwError msg
        | .ok levelParams => do
          let indTypes ← replaceIndFVarsWithConsts views indFVars levelParams numVars numParams indTypes
          let decl := Declaration.inductDecl levelParams numParams indTypes isUnsafe
          Term.ensureNoUnassignedMVars decl
          addDecl decl
          mkAuxConstructions views
    withSaveInfoContext do  -- save new env
      for view in views do
        Term.addTermInfo' view.ref[1] (← mkConstWithLevelParams view.declName) (isBinder := true)
        for ctor in view.ctors do
          Term.addTermInfo' ctor.ref[2] (← mkConstWithLevelParams ctor.declName) (isBinder := true)
        -- We need to invoke `applyAttributes` because `class` is implemented as an attribute.
        Term.applyAttributesAt view.declName view.modifiers.attrs .afterTypeChecking

/-
Paper that describes writing custom parser:
https://eprints.illc.uva.nl/id/eprint/2239/1/MoL-2023-03.text.pdf
GitHub: https://github.com/alexkeizer/qpf4
-/
def Lean.Parser.Command.«bad_inductive» := leading_parser "bad_inductive " >> Lean.Parser.Command.declId >> Lean.Parser.Command.optDeclSig >> Lean.Parser.many Lean.Parser.Command.ctor
@[commandParser] def declaration := leading_parser
Lean.Parser.Command.declModifiers false >> Lean.Parser.Command.«bad_inductive»

-- @[builtinCommandElab declaration]
def elabDeclaration' : CommandElab := fun stx => do
  let decl     := stx[1]
  let declKind := decl.getKind
  if declKind == ``Lean.Parser.Command.«bad_inductive» then
    let modifiers ← elabModifiers stx[0]
    elabInductive modifiers decl
  else
    throwError "unexpected declaration"

private def applyComputedFields (indViews : Array InductiveView) : CommandElabM Unit := do
  if indViews.all (·.computedFields.isEmpty) then return

  let mut computedFields := #[]
  let mut computedFieldDefs := #[]
  for indView@{declName, ..} in indViews do
    for {ref, fieldId, type, matchAlts, modifiers, ..} in indView.computedFields do
      computedFieldDefs := computedFieldDefs.push <| ← do
        let modifiers ← match modifiers with
          | `(Lean.Parser.Command.declModifiersT| $[$doc:docComment]? $[$attrs:attributes]? $[$vis]? $[noncomputable]?) =>
            `(Lean.Parser.Command.declModifiersT| $[$doc]? $[$attrs]? $[$vis]? noncomputable)
          | _ => do
            withRef modifiers do logError "unsupported modifiers for computed field"
            `(Parser.Command.declModifiersT| noncomputable)
        `($(⟨modifiers⟩):declModifiers
          def%$ref $(mkIdent <| `_root_ ++ declName ++ fieldId):ident : $type $matchAlts:matchAlts)
    let computedFieldNames := indView.computedFields.map fun {fieldId, ..} => declName ++ fieldId
    computedFields := computedFields.push (declName, computedFieldNames)
  withScope (fun scope => { scope with
      opts := scope.opts
        |>.setBool `bootstrap.genMatcherCode false
        |>.setBool `elaboratingComputedFields true}) <|
    elabCommand <| ← `(mutual $computedFieldDefs* end)

  liftTermElabM do Term.withDeclName indViews[0]!.declName do
    ComputedFields.setComputedFields computedFields

private def applyDerivingHandlers (views : Array InductiveView) : CommandElabM Unit := do
  let mut processed : NameSet := {}
  for view in views do
    for classView in view.derivingClasses do
      let className := classView.className
      unless processed.contains className do
        processed := processed.insert className
        let mut declNames := #[]
        for view in views do
          if view.derivingClasses.any fun classView => classView.className == className then
            declNames := declNames.push view.declName
        classView.applyHandlers declNames

def elabInductiveViewsUnsafe (views : Array InductiveView) : CommandElabM Unit := do
  let view0 := views[0]!
  let ref := view0.ref
  runTermElabM fun vars => Term.withDeclName view0.declName do withRef ref do
    mkInductiveDecl vars views
    mkSizeOfInstances view0.declName
    Lean.Meta.IndPredBelow.mkBelow view0.declName
    for view in views do
      mkInjectiveTheorems view.declName
  applyComputedFields views -- NOTE: any generated code before this line is invalid
  applyDerivingHandlers views
  runTermElabM fun _ => Term.withDeclName view0.declName do withRef ref do
    for view in views do
      Term.applyAttributesAt view.declName view.modifiers.attrs .afterCompilation

@[commandElab declaration]
def elabData : CommandElab := fun stx => do
  let modifiers ← elabModifiers stx[0]
  let decl := stx[1]
  -- dbg_trace decl
  let view ← badInductiveSyntaxToView modifiers decl
  -- elabInductiveViews #[view]
  elabInductiveViewsUnsafe #[view]

#check InductiveView
bad_inductive test : Type
| a: test
| b : test
| c : test → test

bad_inductive Bad : Type
| a : Type → Bad

#check @test.rec

#check test.a

def x : test → Nat
| .a => 0
| .b => 1
| .c q => x q + 1

-- #eval test `(inductive thing : Type | x : thing)

------------------------------------------------------------------------
#check Lean.Elab.Term.elabMatch

@[builtinTermParser] def «match_with_axioms» := leading_parser:Lean.Parser.leadPrec "«match_with_axioms» " >> Lean.Parser.optional Lean.Parser.Term.generalizingParam >> Lean.Parser.optional Lean.Parser.Term.motive >> Lean.Parser.sepBy1 Lean.Parser.Term.matchDiscr ", " >> " with " >> Lean.Parser.ppDedent Lean.Parser.Term.matchAlts
@[commandParser] def match_decl := leading_parser
Lean.Parser.Command.declModifiers false >> «match_with_axioms»

@[commandElab match_decl]
def elabMatch : TermElab := fun stx expectedType? => do
  sorry
