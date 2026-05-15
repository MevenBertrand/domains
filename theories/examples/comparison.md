# Rocq vs Agda Definitions

Comparison of definitions in the Rocq project (`theories/examples/finelt/`, `theories/examples/syntax/`) versus the Agda project (`../../agda/domain-semantics/`).

| Topic | Rocq (file:definition) | Agda (file:definition) |
|-------|------------------------|------------------------|
| **Raw Syntax** | | |
| Terms | [syntax/syntax.v](../syntax/syntax.v): `Tm` | RawSyntax.agda: `Expr` |
| Finite indices | [syntax/fin_util.v](../syntax/fin_util.v): `f0..f3` | RawSyntax.agda: `Fin` |
| Renaming | [syntax/syntax.v](../syntax/syntax.v): `ren_Tm`, `renRen_Tm` | RawSyntax.agda: `liftRen`, `renExpr` |
| Weakening | [syntax/syntax.v](../syntax/syntax.v): `extRen_Tm` | RawSyntax.agda: `wkRen`, `wkExpr` |
| Substitution | [syntax/syntax.v](../syntax/syntax.v): `subst_Tm`, `substSubst_Tm` | RawSyntax.agda: `liftSub`, `substExpr`, `subst1` |
| **Typing** | | |
| Typing judgment | [syntax/typing.v](../syntax/typing.v): `typing` | TypingRules.agda: `HasType` |
| Conv. judgment | [syntax/typing.v](../syntax/typing.v): `conv` | TypingRules.agda: `ConvTm` |
| Eta conversion | [syntax/typing.v](../syntax/typing.v): `c_eta` constructor of `conv` | EtaConversion.agda: `eta-conv` |
| Beta conversion | [syntax/typing.v](../syntax/typing.v): `c_beta` | TypingRules.agda |
| Contexts | [syntax/typing.v](../syntax/typing.v): `Ctx`, `ctx` | TypingRules.agda: `Ctx`, `WfCtx` |
| Var lookup | [syntax/typing.v](../syntax/typing.v): `lookup` | TypingRules.agda: `lookup` |
| Renaming / subst | [syntax/typing.v](../syntax/typing.v): `typing_renaming`, `renaming_typing`, `typing_subst` | SubstitutionLemma.agda: `RenTypes`, `WtSub` |
| **Finite Elements (Domain)** | | |
| Element datatype | [findom.v](findom.v): `Raw.elt` (7 ctors: `bot`, `tnat`, `tuniv n`, `zero`, `succ`, `tpi a f`, `abs f`) | Basic.agda: `FinEl` (4 ctors: `Bot`, `UCode`, `FunEl g`, `PiCode a f`) |
| Bottom | [findom.v](findom.v): `bot` | Basic.agda: `Bot` |
| Universe code(s) | [findom.v](findom.v): `tuniv : nat -> elt` (universe hierarchy) | Basic.agda: `UCode` (single universe) |
| Naturals | [findom.v](findom.v): `tnat`, `zero`, `succ` | — (no built-in Nat type) |
| Pi-type code | [findom.v](findom.v): `tpi a f` | Basic.agda: `PiCode a f` |
| Function value | [findom.v](findom.v): `abs f` | Basic.agda: `FunEl f` |
| Finite function | [findom.v](findom.v): `list (elt * elt)` | Basic.agda: `FinFun = List (Pair FinEl FinEl)` |
| Rank | [findom.v](findom.v): `rk`, `rk_fun` | Basic.agda: `rk`, `rkFun` |
| Non-bottom | [findom.v](findom.v): `~~ le _ bot` (via `no_bot_result`) | PaperSemantics.agda: `NotBot` |
| **Order & Operations** | | |
| Decidable order on elts | [findom.v](findom.v): `le : elt -> elt -> bool` (boolean) | PaperSemantics.agda: `leFinEl : FinEl -> FinEl -> Nat` (positive = holds) |
| Decidable order on funs | [findom.v](findom.v): `le_fun` (boolean) | PaperSemantics.agda: `leFun` (Nat) |
| Propositional order | [findom.v](findom.v): lifted from boolean (no separate prop. version) | PaperSemantics.agda: `LeCode`, `LeFunCode` (Set-valued) |
| Compatibility | [findom.v](findom.v): `compatible`, `compatible_fun` (boolean) | PaperSemantics.agda: `Comp`, `CompFun`, `CompStepFun`, `CompStepStep` |
| Coherent-with | [findom.v](findom.v): `coherent_with f (u,v)` | PaperSemantics.agda: `CoherentWith` |
| Validity (= coherence) | [findom.v](findom.v): `valid`, `valid_fun` (boolean; `valid_fun` does **not** include `~~ is_bot` since commit `d846fd3`) | PaperSemantics.agda: `Coherent`, `CoherentFun`, `CoherentFunTail` |
| CFT record | [findom.v](findom.v): `Record CFT u v f` (`key_valid`, `val_valid`, `val_nbot`, `compat`) | PaperSemantics.agda: `record CFTcons` (`key-coh`, `val-coh`, `val-nbot`, `compat`, `tail-coh`) |
| Sup / lub | [findom.v](findom.v): `lub : elt -> elt -> option elt` (None on incompat) | PaperSemantics.agda: `Sup : FinEl -> FinEl -> FinEl` (returns `Bot` on incompat) |
| Lub of list | [findom.v](findom.v): `lub_list`, `lub_list_opt` | (inlined via `Sup`/`append`) |
| Append on fns | [findom.v](findom.v): `++` (list append) | PaperSemantics.agda: `append` |
| Apply finite fn | [findom.v](findom.v): `app : list (elt*elt) -> elt -> option elt` | PaperSemantics.agda: `EvalFun : FinFun -> FinEl -> FinEl` |
| Apply elt as fn | [findom.v](findom.v): (via `app` after `abs`-pattern) | PaperSemantics.agda: `applyEl` |
| Refl/trans/mono | [findom.v](findom.v): `le_refl`, `le_trans`, `le_fun_mono`, `OrderTheoreticLemmas` | PaperSemantics.agda: stated as separate lemmas |
| **Well-typed elements (codes)** | | |
| Membership relation | [types.v](types.v): `wt : elt -> elt -> Prop` (inductive: `wt_bot`, `wt_tuniv`, `wt_tnat`, `wt_zero`, `wt_succ`, `wt_tpi`, `wt_abs`) | Basic.agda: `FinMem`, `FinMemU` |
| `is_type` | [types.v](types.v): `is_type` inductive | — |
| Level / rank | [types.v](types.v): `level`, `level_fun`, `level_le` | Basic.agda: `rk`, `rkFun` |
| **Raw Semantics** | | |
| Environment | [raw_semantics.v](raw_semantics.v): `Env n := fin n -> elt` | RawSemantics.agda: `EnvApprox` |
| Evaluation | [raw_semantics.v](raw_semantics.v): `EvalRel`, `EvalRel_fun` | RawSemantics.agda: `EvalRel` |
| Bottom test | [findom.v](findom.v) / [raw_semantics.v](raw_semantics.v): `is_bot` | PaperSemantics.agda: `NotBot` (negation) |
| Singleton fn | [findom.v](findom.v): `singleton a b` (`= bot` if `b = bot`) | (built inline via `cons (a,b) nil`) |
| Env validity | [raw_semantics.v](raw_semantics.v): `valid_env` | RawSemantics.agda: `CoherentEnv` |
| Env order | [raw_semantics.v](raw_semantics.v): `le_env` | RawSemantics.agda: `EnvLe` |
| Eval monotonicity | [raw_semantics.v](raw_semantics.v): `EvalRel_mono_env`, `EvalRel_down`, `EvalRel_sup`, `EvalRel_valid`, `lam_edgewise`, `EvalRel_fun_compatible` | (analogues in RawSemantics.agda / Validity.agda) |
| Eval renaming/subst | [eval_substitution.v](eval_substitution.v): `EvalRel_unwk`, `EvalRel` renaming/subst lemmas | EvalSubstitution.agda: `SubRel`, `extractFinMemU` |
| **Logical relation V2** (recursive on `wt`) | | |
| Module | [raw_validity2.v](raw_validity2.v) | Validity2.agda |
| Head reduction | [raw_validity2.v](raw_validity2.v): `HeadRed1`, `HeadRed`, `HeadRed_tpi_det`, `HeadRed1_det` | Reduction.agda: `HeadRed`, `HeadRed1` |
| `wt`-inversion for `tpi`/`abs` | [raw_validity2.v](raw_validity2.v): `wt_tpi_dom`, `wt_tpi_cod_key`, `wt_tpi_cod_elt`, `wt_abs_dom`, `wt_abs_key`, `wt_abs_elt`, `wt_succ_inv` | (built-in via pattern matching) |
| Unary value relation | [raw_validity2.v](raw_validity2.v): `Val M A (h : wt u a)` (Fixpoint on `h`) | Validity2.agda: `Val2` |
| Binary equality relation | [raw_validity2.v](raw_validity2.v): `EqVal M N A h` (mutual Fixpoint) | Validity2.agda: `EqVal2` |
| Type-relations | [raw_validity2.v](raw_validity2.v) (`Rec.` namespace): `ValTy`, `EqValTy` | Validity2.agda: `ValTy2`, `EqValTy2` |
| Pi-edge predicates | [raw_validity2.v](raw_validity2.v): `PiEdgeVal`, `PiEdgeEq` (forall edge `(u,v)` in pi-fn) | Validity2.agda: `PiEdgeVal2`, `PiEdgeEq2` |
| Pi-app predicates | [raw_validity2.v](raw_validity2.v): `PiAppVal`, `PiAppEq`, `PiAppEqVal` (forall edge `(u,v)` in lambda-fn) | Validity2.agda: `PiAppVal2`, `PiAppEq2`, `PiAppEqVal2` |
| Pi value predicate | [raw_validity2.v](raw_validity2.v): `ValPi`, `EqValPi` (exists `(A,B)` such that `HeadRed` to `tpi A B`) | Validity2.agda: `ValPi2`, `EqValPi2` |
| Bot lemmas | [raw_validity2.v](raw_validity2.v): `Val_Bot`, `EqVal_Bot` | Validity2.agda: `Val2-Bot`, `EqVal2-Bot` |
| Val ↔ ValTy / EqVal ↔ EqValTy | [raw_validity2.v](raw_validity2.v): `ValTy_Val`, `Val_ValTy`, `EqValTy_EqVal`, `EqVal_EqValTy` | Validity2.agda (named the same with `2` suffix) |
| Diagonal | [raw_validity2.v](raw_validity2.v): `Val_EqVal`, `ValTy_EqValTy` | Validity2.agda |
| Projections | [raw_validity2.v](raw_validity2.v): `EqVal_Val1`, `EqVal_Val2` | Validity2.agda |
| Symmetry/transitivity | [raw_validity2.v](raw_validity2.v): `EqVal_sym`, `EqVal_trans`, `EqValTy_sym`, `EqValTy_trans` | Validity2.agda |
| Forward by type-eq | [raw_validity2.v](raw_validity2.v): `Val_EqVal_fwd`, `EqVal_EqVal_fwd` | Validity2.agda |
| Head-red expand/contract | [raw_validity2.v](raw_validity2.v): `ValTy_headred_expand/contract`, `EqValTy_headred_expand/contract`, `Val_beta_expand`, `Val_headred_contract`, `EqVal_headred_expand/contract`, `ValPi_headred_expand/contract`, `EqValPi_headred_expand/contract` | Validity2.agda (corresponding names) |
| Sup | [raw_validity2.v](raw_validity2.v): `ValTy_Sup`, `EqValTy_Sup` | Validity2.agda: `ValTy2-Sup`, `EqValTy2-Sup` |
| Up / Down | [raw_validity2.v](raw_validity2.v): `upVal`, `upEqVal`, `downVal`, `downEqVal`, `downValTy`, `downEqValTy` | Validity2.agda |
| Restrict | [raw_validity2.v](raw_validity2.v): `restrictVal`, `restrictEqVal` | Validity.agda: `restrictVal` |
| Pi helpers | [raw_validity2.v](raw_validity2.v): `downPiAppVal/Eq/EqVal`, `upPiAppVal/Eq/EqVal`, `transportPiEdgeVal/Eq/EqTy_sel`, `restrictPiAppVal/Eq/EqVal_sel`, `restrictVal/EqVal_PiCode` | Validity2.agda |
| **Semantic Validity (envs/contexts)** | | |
| Fits relation | [typing_semantics.v](typing_semantics.v): `fits` (env matches Ctx in `wt`) | RawSemantics / LemmaForTS.agda: `Fits` |
| Typed predicate | [typing_semantics.v](typing_semantics.v): `Typed`, `InvTyped`, `InvConv` | TypingSemantics.agda |
| Inversion helpers | [typing_semantics.v](typing_semantics.v): `Lam_L1`, `Pi_L1`, `InvTyp_Pi`, `InvTyp_Lam`, `InvTyp_Lam'`, `InvTyp_App`, `InvConv_App_fun/arg`, `InvConv_Pi`, `InvConv_beta`, `InvConv_funext` | LemmaForTS.agda |
| Soundness theorem | [typing_semantics.v](typing_semantics.v): `typing_EvalRel`, `typing_EvalRel'` | TypingSemantics.agda: corresponding theorem |
| Pi application | [raw_validity2.v](raw_validity2.v): `PiAppVal`, `PiAppEq` | Validity.agda: `PiAppVal`, `PiAppEq` |
| Projection / restrict | [raw_validity2.v](raw_validity2.v): `downVal`, `upVal`, `restrictVal` | Validity.agda: `downVal`, `upVal`, `restrictVal` |
| **Adequacy & corollaries** | | |
| Sub validity (closing) | [adequacy.v](adequacy.v): `ValSub`, `ValSub_empty`, `ValSub_cons` | Adequacy2.agda: `ValidSub2`, `ValidSub2-empty`, `ValidSub2-extend` |
| Conv-sub validity | [adequacy.v](adequacy.v): `EqValSub`, `EqValSub_empty`, `EqValSub_cons`, `ValSub_EqValSub` | Adequacy2.agda: `ValidConvSub2`, `ValidConvSub2-refl`, `ValidConvSub2-extend` |
| Semantic typing | [adequacy.v](adequacy.v): `semantic_typing`, `semantic_conv`, `semantic_conv2` | Adequacy2.agda: corresponding judgments |
| Sem. typing rules | [adequacy.v](adequacy.v): `st_var`, `st_conv`, `st_abs`, `st_app` (admitted/in progress) | Adequacy2.agda: `adequacy2` (proved) |
| Adequacy theorem | [adequacy.v](adequacy.v) (stated; bulk admitted) | Adequacy2.agda: `adequacy2` |
| Bot environment | [adequacy.v](adequacy.v): `bot_env_lookup/cons/null`, `fits_bot_env`, `evalRel_Pi_trivial` | PiInjectivity.agda: `botEnv`, `botEnv-coherent`, `botEnv-lookup`, `botEnv-fits` |
| Pi conversion | [adequacy.v](adequacy.v): `piConv` (admitted) | PiInjectivity.agda: `piConv` |
| Pi injectivity | [adequacy.v](adequacy.v): `piInjectivity` (proved from `piConv`) | PiInjectivity.agda: `piInjectivity` |
| **Reduction** | | |
| Multi-step reduction | [syntax/relations.v](../syntax/relations.v): `step_n`, `multi` | Reduction.agda: `Red` |

## Notes

- **Element datatype.** Rocq's `Raw.elt` is richer at the constructor level: it has primitive `tnat`/`zero`/`succ` for natural numbers and a universe hierarchy `tuniv : nat -> elt`. Agda's `FinEl` collapses these into a single `UCode`, and naturals are absent from the domain. Both share the function/Pi shape (`abs f` ↔ `FunEl g`, `tpi a f` ↔ `PiCode a f`).
- **Order representation.** Agda represents order in two layers: a Nat-valued decidable check (`leFinEl`/`leFun`, positive = holds) and a Set-valued propositional version (`LeCode`/`LeFunCode`). Rocq fuses both: `le`/`le_fun` are `bool`-valued and serve as both decision procedure and proposition (via `is_true`/coercion). Both require an explicit termination metric — Agda uses `{-# TERMINATING #-}` on the mutual block; Rocq passes `max (rk u) (rk v)` as a fuel argument to `le'`.
- **`valid_fun` (commit `d846fd3`).** Rocq's `valid_fun` no longer requires non-bot results (`~~ is_bot` was dropped); non-bot is enforced where needed (e.g., the `abs g` case of `EvalRel` adds `~~ is_nil g`). This aligns it more closely with Agda's `CoherentFun`, which is the pure pairwise/recursive coherence predicate.
- **`EvalRel` for λ and Π (recent refactor).** The Rocq `EvalRel` clauses for `abs A M` and `tpi A B` were restructured: the lambda case now carries `valid_fun g /\ ~~ is_nil g` (so a λ never evaluates to an empty function), and the Pi case carries `valid_fun g` plus an unconditional edgewise body, replacing the prior `is_nil g \/ EvalRel_fun B ρ a g` disjunction.
- **Compatibility vs. validity.** Agda's `Comp`/`CompFun` is the symmetric pairwise compatibility predicate; Rocq calls this `compatible`/`compatible_fun`. Agda's `Coherent`/`CoherentFun`/`CoherentFunTail` corresponds to Rocq's `valid`/`valid_fun`. The Agda record `CFTcons` is exactly the Rocq record `CFT` (`key-coh`/`val-coh`/`val-nbot`/`compat` matching `key_valid`/`val_valid`/`val_nbot`/`compat`).
- **Sup vs. lub.** Both compute the binary supremum, but Agda's `Sup` returns `Bot` on incompatible pairs while Rocq's `lub` returns `option elt` (`None` on incompatible). The distinction matters: Rocq can detect "no lub exists"; Agda silently defaults to bottom and relies on coherence preconditions.
- **EvalFun vs. app.** Both compute `f(u) = ⊔ { vᵢ | uᵢ ≤ u }` from the paper. Agda's `EvalFun` returns `FinEl` (using `Sup`); Rocq's `app` returns `option elt` (using `lub_list`).
- **Validated/quotient layer.** Rocq adds two layers on top of `Raw.elt` that have no Agda counterpart: `Valid.elt` (sigma-types of valid raws) and `Q.elt` (quotient by `eqb`). These give a setoid/quotient model with respected operations. Agda stays at the raw level and threads coherence as side conditions.
- **Eta.** Both sides now have an explicit eta rule. Rocq's eta is a constructor `c_eta` of the mutual `conv` judgment in [syntax/typing.v](../syntax/typing.v); Agda's is `eta-conv` in `EtaConversion.agda`.
- **Definitional equality.** Both sides now have an explicit definitional-equality judgment: Rocq's `conv` (mutually inductive with `typing` in [syntax/typing.v](../syntax/typing.v)) corresponds to Agda's `ConvTm`. The semantic counterpart on each side is `EqVal` (Rocq's `raw_validity2.Val/EqVal` mirroring Agda's `Validity2.Val2/EqVal2`).
- **Membership.** Both sides factor the relation through the codes. Agda uses `FinMem u a` (recursive on `a`); Rocq's older `Val u a` in [raw_validity.v](raw_validity.v) plays the same role, and the newer [raw_validity2.v](raw_validity2.v) instead recurses on a typing derivation `(h : wt u a)`. The recursion-on-derivation style avoids the "type encoded twice" issue but forces all auxiliary lemmas (up/down/restrict/headred) into the same mutual block (Level 6 SCC, ~30 lemmas — see the topology comment in [raw_validity2.v](raw_validity2.v#L944-L1017)).
- **Substitution.** Heavily mechanized in Rocq's [syntax/syntax.v](../syntax/syntax.v) (Autosubst-style); Agda factors it through Selection/SubstitutionLemma/EvalSubstitution. Renaming/substitution lemmas for `EvalRel` live in [eval_substitution.v](eval_substitution.v) (Rocq) and `EvalSubstitution.agda` (Agda).
- **Adequacy & Pi injectivity.** Both sides now state these. On the Agda side `adequacy2` and `piInjectivity` are proved; on the Rocq side [adequacy.v](adequacy.v) develops the same shape (`ValSub`, `EqValSub`, `semantic_typing`, `semantic_conv2`, semantic typing rules `st_var/st_conv/st_abs/st_app`, plus the `bot_env`/`piConv`/`piInjectivity` corollary chain) but most lemmas other than `st_var`, `ValSub_EqValSub`, `fits_bot_env`, `evalRel_Pi_trivial`, and `piInjectivity` (which is reduced to the admitted `piConv`) currently have `Admitted` proofs.
- **Status.** The recursion-on-`wt` logical relation (`Val`/`EqVal` in [raw_validity2.v](raw_validity2.v)) is fully defined and many of its closure lemmas are proved (Bot, Val↔ValTy, EqVal_Val1/Val2, diagonal `Val_EqVal`, head-red transports across the universe levels, up/down/restrict for some constructors, sup, symmetry/transitivity). Termination of the Level-6 SCC is still being worked through; several Pi-specific cases (`restrictVal` on PiCode, `Val_EqVal_fwd` on the Pi case, `Val_beta_expand`, head-red contractions for `Val`/`EqVal`/`ValPi`/`EqValPi`) are stated with `Admitted`.
