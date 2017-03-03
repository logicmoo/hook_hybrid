/* Part of LogicMOO Base logicmoo_util_bb_env
% Provides a prolog database *env*
% ===================================================================
% File '$FILENAME.pl'
% Purpose: An Implementation in SWI-Prolog of certain debugging tools
% Maintainer: Douglas Miles
% Contact: $Author: dmiles $@users.sourceforge.net ;
% Version: '$FILENAME.pl' 1.0.0
% Revision: $Revision: 1.1 $
% Revised At:  $Date: 2002/07/11 21:57:28 $
% Licience: LGPL
% ===================================================================
*/

% File: /opt/PrologMUD/pack/logicmoo_base/prolog/logicmoo/util/logicmoo_util_structs.pl
:- module(virtualize_source,
          [
          'decl_kb_shared'/1,
          decl_as/2,
          virtualize_source/3,
          virtualize_code/3,
          virtualize_code_fa/5,
          virtualize_code_each/4,
          virtualize_ereq/2,
          safe_virtualize/3,
          sd_goal_expansion/3,
          ereq/1,
          dbreq/1,
          swc/0,
          vwc/0,
          check_mfa/3,
          nb_current_or_nil/2,
          skipped_dirs/1,
          ignore_mpreds_in_file/1,
          ignore_mpreds_in_file/0,
          (kb_shared)/1,
          clause_b/1,
          same_terms/2,          
          warn_if_static/2]).


:- set_module(class(library)).

:- if( \+ current_op(_,_,(kb_shared))).

:- current_prolog_flag(access_level,Was),
   set_prolog_flag(access_level,system),
   op(1150,fx,(kb_shared)),
   set_prolog_flag(access_level,Was).

:- endif.


:- module_transparent((
                    'decl_kb_shared'/1,decl_as/2,(kb_shared)/1,
          virtualize_source/3,
          virtualize_code/3,
          virtualize_code_fa/5,
          ereq/1,
          dbreq/1,
          swc/0,
          vwc/0,
          check_mfa/3,
          skipped_dirs/1,
          ignore_mpreds_in_file/1,
          ignore_mpreds_in_file/0,
          clause_b/1,
          warn_if_static/2)).

:- module_transparent((virtualize_ereq_source/0)).

:- meta_predicate decl_as(1,+).
:- meta_predicate decl_as_rev(+,+).
:- meta_predicate map_compound_args(3,*,*,*).
:- meta_predicate map_compound_args(2,*,*).

:- module_transparent(declared_to_wrap/3).

:- multifile(t_l:disable_px/0).
:- thread_local(t_l:disable_px/0).


nb_current_or_nil(N,V):- notrace((nb_current(N,V)->true;V=[])).

:- multifile(baseKB:col_as_isa/1).
:- multifile(baseKB:col_as_unary/1).
:- multifile(baseKB:col_as_static/1).
:- dynamic(baseKB:col_as_isa/1).
:- dynamic(baseKB:col_as_unary/1).
:- dynamic(baseKB:col_as_static/1).

:- dynamic(ereq/1).
:- module_transparent(ereq/1).
ereq(C):- find_and_call(C).

:- dynamic(dbreq/1).
:- module_transparent(dbreq/1).
dbreq(C):- ereq(C).

:- multifile(baseKB:ignore_file_mpreds/1).
:- dynamic(baseKB:ignore_file_mpreds/1).

:- asserta((baseKB:ignore_file_mpreds(M):- skipped_dirs(M))).

skipped_dirs(M):-expand_file_search_path(swi(''),M),nonvar(M).
skipped_dirs(M):-expand_file_search_path(pack(logicmoo_util),M),nonvar(M).
% skipped_dirs(M):-expand_file_search_path(pack(pfc),M),nonvar(M).


ignore_mpreds_in_file:-if_defined(t_l:disable_px,fail),!.
ignore_mpreds_in_file:-prolog_load_context(file,F),ignore_mpreds_in_file(F),!.
ignore_mpreds_in_file:-prolog_load_context(source,F),ignore_mpreds_in_file(F),!.

ignore_mpreds_in_file(F):-if_defined(baseKB:registered_mpred_file(F),fail),!,fail.
ignore_mpreds_in_file(F):-if_defined(baseKB:ignore_file_mpreds(F),fail),!.
ignore_mpreds_in_file(F):-skipped_dirs(Base),atom(Base),atom_concat(Base,_,F),!.
ignore_mpreds_in_file(F):-atom(F),baseKB:ignore_file_mpreds(Base),atom(Base),atom_concat(Base,_,F),!.

%% declared_to_wrap( ?Functor, ?Arity, ?Wrapper) is semidet.
%
% Virtualizer Shared Code.
%

get_virtualizer_mode(ge,F,A,HowIn):- declared_to_wrap(F,A,HowOut),!,must(HowIn=HowOut),HowOut\==never.

:- multifile(baseKB:safe_wrap/3).
:- dynamic(baseKB:safe_wrap/3).

declared_to_wrap(O,_,_):- bad_functor_check(O),!,fail.
declared_to_wrap(F,A,HowIn):- clause_b(safe_wrap(F,A,HowIn)),!.
declared_to_wrap(mtCycL,1,clause_b).
declared_to_wrap(F,A,on_x_debug):- integer(A),virtualize_safety(F,A).
declared_to_wrap(F,A,dbreq):- virtualize_dbreq(F,A), virtualize_dbreq_source.
declared_to_wrap(F,A,ereq):- clause_b(mpred_prop(F,A,prologHybrid)),!.
declared_to_wrap(F,A,ereq):- virtualize_ereq(F,A), virtualize_ereq_source.
declared_to_wrap(F,A,_):- prolog_load_context(module,M),never_virtualize(M:F/A),!,fail.
declared_to_wrap(F,A,_):-      clause_b(mpred_prop(F,A,prologBuiltin)),!,fail.
declared_to_wrap(F,A,call_u):- clause_b(mpred_prop(F,A,_)),!.

declared_to_wrap(F,A,ereq):- atom(F),integer(A),
   functor(Goal,F,A),
   % member(M,[baseKB,lmcache,lmconf]),
   baseKB = M,
   predicate_property(M:Goal,defined),
   \+ predicate_property(M:Goal,static),
   \+ predicate_property(M:Goal,imported_from(_)),!.




is_dynamic_module(user).
is_dynamic_module(baseKB).
is_dynamic_module(lmcache).
is_dynamic_module(lmconf).
is_dynamic_module(tlbugger).
is_dynamic_module(t_l).
is_dynamic_module(prolog).
is_dynamic_module(eggdrop).
is_dynamic_module(M):- clause_b(mtCycL(M)).

is_static_module(system).
is_static_module(file_scope).
is_static_module(mpred_core).
is_static_module(M):- is_dynamic_module(M),!,fail.
is_static_module(M):- module_property(M,class(development)),!,fail.
is_static_module(M):- module_property(M,class(library)),!.
is_static_module(M):- module_property(M,class(system)),!.

% virtualize_dbreq_source :- prolog_load_context(module,M), (atom_concat('common_logic_',_,F);atom_concat('logicmoo_',_,F);atom_concat('mpred_',_,F)),!.
virtualize_dbreq_source :- prolog_load_context(source,F), 
  (atom_concat('common_logic_',_,F);atom_concat('logicmoo_',_,F);atom_concat('mpred_',_,F)),!.
virtualize_dbreq_source :- prolog_load_context(module,M), \+ is_static_module(M).
% virtualize_dbreq_source.

virtualize_ereq_source :- prolog_load_context(module,M), member(M,['mpred_core','mpred_expansion']),!,fail.
virtualize_ereq_source.

bad_functor_check(O):-var(O).
bad_functor_check(:):- !,dumpST,dtrace.
%bad_functor_check(/):- !,dumpST,dtrace.
%bad_functor_check(//):- !,dumpST,dtrace.


% Preds that we''d like to know a little more than "instanciation exception"s
virtualize_safety(O,_):- bad_functor_check(O),!,fail.

/*
virtualize_safety((=..),2).
virtualize_safety(functor,3).
virtualize_safety(is,2).
virtualize_safety(arg,3).
*/

% Preds that we assume indicate we''d already passed over it


never_virtualize(O):- bad_functor_check(O),!,fail.
never_virtualize(ereq).
never_virtualize(call_u).
never_virtualize(clause_u).
never_virtualize(lookup_u).
never_virtualize(dbreq).
never_virtualize(clause_b).
never_virtualize(('.')).
never_virtualize(('[]')).
never_virtualize(('[|]')).
never_virtualize(add).
never_virtualize(padd).
never_virtualize(del).
never_virtualize(ain_expanded).
never_virtualize(meta_predicate).
never_virtualize(dynamic).
never_virtualize(clr).
never_virtualize(ain).
never_virtualize(props).
never_virtualize(=).
never_virtualize(==).
never_virtualize(iprop).
never_virtualize(aina).
never_virtualize(decl_as).
never_virtualize(ainz).
never_virtualize((':-')).
never_virtualize(_:','/2):-!,fail.
never_virtualize(thread_util:_/A):-integer(A). % prevents query
%never_virtualize(F):- clause_b(mpred_prop(F,_,pfcBuiltin)). % @todo not yet created
%never_virtualize(F):- show_success(plz_never_virtualize(F)).

never_virtualize(Atom):- never_virtualize2(Atom).
never_virtualize(Atom):- atom(Atom),!,atom_concat('mpred_',_,Atom). % mpred_* are pfc builtins

never_virtualize(_:FA):- never_virtualize(FA),!.
never_virtualize(F/A):- clause_b(mpred_prop(F,A,prologBuiltin)),!.
never_virtualize(F/_):- never_virtualize(F),!.
never_virtualize(F/A):- current_predicate(mpred_core:F/A),!.
never_virtualize(F/A):- functor(P,F,A),source_file(M:P,_SF), 
   \+ predicate_property(M:P,meta_predicate(_)), 
   \+ predicate_property(M:P,transparent),  
  % dmsg(never_virtualize('@'(F/A,M),SF)),
  ain(baseKB:mpred_prop(F,A,prologBuiltin)). 
  
never_virtualize(M:F/A):- functor(P,F,A),source_file(M:P,SF),
   \+ predicate_property(M:P,meta_predicate(_)), 
   \+ predicate_property(M:P,transparent),  
  dmsg(never_virtualize(M:F/A,SF)),aina(baseKB:mpred_prop(F,A,prologBuiltin)).


never_virtualize2((/)).
never_virtualize2((//)).
never_virtualize2(call).
never_virtualize2(apply).

plz_never_virtualize(on_x_debug).


% operations to transactionalize
virtualize_dbreq(O,_):- bad_functor_check(O),!,fail.
virtualize_dbreq(abolish,1).
virtualize_dbreq(abolish,2).
virtualize_dbreq(assert,1).
virtualize_dbreq(assert,2).
virtualize_dbreq(asserta,1).
virtualize_dbreq(asserta,2).
virtualize_dbreq(assertz,1).
virtualize_dbreq(assertz,2).
virtualize_dbreq(nth_clause,3).
virtualize_dbreq(clause,2).
virtualize_dbreq(clause,3).
virtualize_dbreq(retract,1).
virtualize_dbreq(listing,1).
virtualize_dbreq(clause_property,2).
virtualize_dbreq(retractall,1).
virtualize_dbreq(recorda,_).
virtualize_dbreq(recordz,_).
virtualize_dbreq(recorded,_).
virtualize_dbreq(erase,1).




virtualize_ereq(O,_):- bad_functor_check(O),!,fail.

%virtualize_ereq(lmcache:loaded_external_kbs,1).

virtualize_ereq(COL,A):- clause_b(col_as_isa(COL)),sanity(A==1).
virtualize_ereq(COL,A):- clause_b(col_as_unary(COL)),sanity(A==1).

virtualize_ereq(isa,2).
virtualize_ereq(genls,2).
virtualize_ereq(t,_).
virtualize_ereq(t,3).

virtualize_ereq(functorDeclares,1).

virtualize_ereq(mtCore,1).
virtualize_ereq(mtProlog,1).
virtualize_ereq(mtCycL,1).
virtualize_ereq(mtExact,1).
virtualize_ereq(mtGlobal,1).
virtualize_ereq(nameString,2).


virtualize_ereq(arity,2).
virtualize_ereq(argIsa,3).
virtualize_ereq(argQuotedIsa,3).
virtualize_ereq(cyckb_t_e2c,3).
virtualize_ereq(cyckb_t_e2c,4).
virtualize_ereq(cyckb_t_e2c,_).


virtualize_ereq(call_OnEachLoad,1).
virtualize_ereq(completeExtentEnumerable,1).
virtualize_ereq(completelyAssertedCollection,1).
virtualize_ereq(constrain_args_pttp,2).
virtualize_ereq(cycPlus2,2).
virtualize_ereq(cycPred,2).
virtualize_ereq(decided_not_was_isa,2).
virtualize_ereq(lambda,5).

virtualize_ereq(meta_argtypes,1).
virtualize_ereq(mpred_f,4).
virtualize_ereq(mpred_f,5).
virtualize_ereq(mpred_f,6).
virtualize_ereq(mpred_f,7).
virtualize_ereq(props,2).

virtualize_ereq(mpred_prop,3).
virtualize_ereq(mudKeyword,2).

virtualize_ereq(pfcControlled,1).
virtualize_ereq(pfcRHS,1).
virtualize_ereq(predicateConventionMt,2).
virtualize_ereq(prologBuiltin,1).
virtualize_ereq(prologDynamic,1).
virtualize_ereq(prologHybrid,1).
virtualize_ereq(prologKIF,1).
virtualize_ereq(functorIsMacro,1).
virtualize_ereq(prologPTTP,1).
virtualize_ereq(prologSideEffects,1).

virtualize_ereq(resultIsa,2).
virtualize_ereq(singleValuedInArg,2).
virtualize_ereq(spft,3).
virtualize_ereq(support_hilog,2).
virtualize_ereq(tCol,1).
virtualize_ereq(rtNotForUnboundPredicates,1).
virtualize_ereq(tPred,1).
virtualize_ereq(tRelation,1).
virtualize_ereq(tAgent,1).
virtualize_ereq(tCol,1).

virtualize_ereq(ttExpressionType,1).
virtualize_ereq(ttRelationType,1).
virtualize_ereq(ttTemporalType,1).
virtualize_ereq(use_ideep_swi,0).
virtualize_ereq(==>,_).
virtualize_ereq(<==>,_).
virtualize_ereq((<--),2).
virtualize_ereq(agent_text_command,_).
virtualize_ereq(agent_command,_).
virtualize_ereq(coerce_hook,_).

:- dynamic(baseKB:t/2).

%% clause_b( ?C) is semidet.
%
% Clause User Microtheory.
%
%clause_b(M:Goal):-  !,clause(M:Goal,true).
%clause_b(Goal):-  !,clause(baseKB:Goal,true).

% lookup_u/cheaply_u/call_u/clause_b
%clause_b(Goal):-  baseKB:call(call,Goal).
clause_b(Goal):-  baseKB:clause(Goal,true).
% clause_b(Goal):-  baseKB:clause(Goal,B),baseKB:call(B).

%clause_b(Goal):-  baseKB:clause(Goal,B)*->call(B);clause_b0(Goal).
%clause_b(Goal):-  baseKB:clause(Goal,true)*->true;clause_b0(Goal).

% clause_b0(Goal):- if_defined(to_was_isa(clause_b,Goal,P0),fail),!,Goal\=P0,baseKB:clause(P0,true).

%clause_b(M:C):-!,clause(M:C,true).
%clause_b(C):- call_u(clause(C,true)).
%clause_b(C):-!,clause(_:C,true).
%clause_b(Goal):-  Goal=..[C,PART],!,baseKB:t(C,PART).
%clause_b(Goal):-  current_predicate(_,baseKB:Goal),!,loop_check(baseKB:Goal).
% clause_b(Goal):- clause(baseKB:Goal,Body),(Body==true->true;call_u(Body)).


%% virtualize_code(X, :TermT, :TermARG2) is semidet.
%
% System Goal Expansion Sd.f$
%

%virtualize_code(X,Goal,_):- functor(Goal,F,_),arg(_,v(call_u,call,(/),(',')),F),!,fail.
%virtualize_code(X,M:Goal,(call_u(genlMt(abox,GMt)),with_umt(GMt,Goal))):- M==tbox.

virtualize_args_as(Goal,Args):- sanity((arg(1,Goal,Var),var(Var))), predicate_property(Goal,meta_predicate(Args)).
virtualize_args_as(Goal,_):-predicate_property(Goal,built_in),!,fail.
virtualize_args_as(Goal,Goal):-predicate_property(Goal,transparent),!.
virtualize_args_as(Which,Args):- descend_ge(Which),Args=Which.

descend_ge(':-'((:),0)).
descend_ge(':-'((-),0)).
descend_ge(( :- 0)).
descend_ge('{}'(0)).
descend_ge('==>'(-,-)).
descend_ge('==>'(-)).
descend_ge('<--'(-,-)).
descend_ge(z(if)).
descend_ge(z(_)):-!,fail.
descend_ge(Which):-functor(Which,F,_),!,descend_ge(z(F)),!.

:- nb_linkval('$xform_arity',xform_arity(_C,_F,_A)).

xform_arity(C,F,A):-var(C),!,sanity(var(F)),must(var(A)), nb_getval('$xform_arity',xform_arity(C,F,A)),!.
xform_arity(C,F,A):-atom(C),!,C=F,ignore(clause_b(arity(F,A))).
xform_arity(F/A,F,A):-atom(F),!.
xform_arity(F//Am2,F,A):- integer(Am2),!, A is Am2+2.
xform_arity(C,F,A):- compound(C), functor(C,F,A).

xform(_,_):-!,fail.
xform(Var,Out):- \+compound(Var),!,Out=Var.
xform(Nonvar,Out):- \+ current_prolog_flag(lm_expanders,true),!,Nonvar=Out.
%xform(isa(C,P),mpred_prop(F,A,P)):-nonvar(P),!,is_reltype(P),xform_arity(C,F,A).
%xform(isa(C,P),(ttRelationType(P),mpred_prop(F,A,P))):-nonvar(C),xform_arity(C,F,A),is_reltype(P),!.
xform(mpred_isa(C,P),mpred_prop(F,A,P)):- xform_arity(C,F,A),!.
xform(hybrid_support(F,A),mpred_prop(F,A,prologHybrid)):-!.
% xform(arity(F,A),mpred_prop(F,A,arity)):-!.
xform(mpred_prop(F,A,P),mpred_prop(F,A,P)):-!.
xform(PC,mpred_prop(F,A,P)):- PC=..[P,C],is_reltype(P),!,xform_arity(C,F,A).
xform(PFA,mpred_prop(F,A,P)):- PFA=..[P,F,A],is_reltype(P),!.
xform(In,PART):- map_compound_args(xform,In,PART),!.

:-multifile(baseKB:ttRelationType/1).
:-dynamic(baseKB:ttRelationType/1).
is_reltype(Var):-var(Var),!,fail.
is_reltype(pfcControlled).
is_reltype(prologHybrid).
is_reltype(prologBuiltin).
is_reltype(P):-clause_b(ttRelationType(P)).


cannot_descend_expansion(_,In):- \+ compound(In),!.
cannot_descend_expansion(ge,In):- strip_module(In,M,FA),functor(FA,F,A),!,never_virtualize(M:F/A).


virtualize_code(_,In,In):- \+ compound(In),!.
virtualize_code(_,(SWC,REST),(SWC,REST)):- (swc==SWC /* ;cwc==SWC */),!. % never goal expand
virtualize_code(X,(VWC,In),(Out)):- vwc==VWC,!,virtualize_code(X,In,Out).
virtualize_code(X,(G1,G2),(O1,O2)):- !,virtualize_code(X,G1,O1),!,virtualize_code(X,G2,O2),!.
virtualize_code(X,\+ G1,\+ O1):- !,virtualize_code(X,G1,O1),!.
virtualize_code(X,setof(In,G1,Out),setof(In,O1,Out)):- virtualize_code(X,G1,O1),!.
virtualize_code(X,(G1;G2),(O1;O2)):- !,virtualize_code(X,G1,O1),!,virtualize_code(X,G2,O2),!.
virtualize_code(X,(G1->G2),(O1->O2)):- !,virtualize_code(X,G1,O1),!,virtualize_code(X,G2,O2),!.
virtualize_code(ge,M:In,ereq(In)):- M==abox,!.
virtualize_code(ge,M:In,M:In):- atom(M),callable(In),(predicate_property(M:In,volatile);predicate_property(M:In,thread_local)),!.
virtualize_code(X,M:In,M:Out):- must(virtualize_code(X,In,Out)),!.
virtualize_code(X,M:In,M:Out):- '$set_source_module'(SM,M),call_cleanup(must(virtualize_code(X,In,Out)),'$set_source_module'(SM)).
virtualize_code(X,In,PART):- functor(In,F,A),virtualize_code_fa(X,In,F,A,PART),!.
%virtualize_code(X,In,PART):- must(map_compound_args(virtualize_code(X),In,PART)),!.
virtualize_code(ge,In,In).
virtualize_code(X,In,PART):- wdmsg(bad_virtualize_code(X,In,PART)), dtrace.

virtualize_code_fa(X,In,_,_,In):- cannot_descend_expansion(X,In),!. % ,fail. % wdmsg(cannot_descend_expansion(X,In))
virtualize_code_fa(X,In,F,A,PART):- get_virtualizer_mode(X,F,A,How),!,must(safe_virtualize(In,How,PART)).
virtualize_code_fa(X,M:In,F,A,M:PART):-!,virtualize_code_fa(X,In,F,A,PART).
virtualize_code_fa(X,In,F,A,PART):- X==ge, functor(ArgModes,F,A),
  Args=ArgModes,
  virtualize_args_as(Args,ArgModes),!, 
  map_compound_args(virtualize_code_each(X),ArgModes,In,PART),!.

% virtualize_code(X,In,Out):- compound(In), virtualize_special_outside(X,In),!,Out=ereq(In).

virtualize_special_outside(X,In):- functor(In,F,A),get_virtualizer_mode(X,F,A,_How),!.
virtualize_special_outside(X,In):- arg(_,In,Arg), \+cannot_descend_expansion(X,Arg),virtualize_special_outside(X,In).

virtualize_code_each(X,Arg,In,Out):- var(Arg),!,virtualize_code_each(X,(+),In,Out).
virtualize_code_each(X,Arg,In,Out):- (integer(Arg); Arg == + ) -> virtualize_code(X,In,Out),!.
virtualize_code_each(X,-,In,Out):- current_predicate(mpred_expansion_file/0), if_defined(fully_expand_head(X,In,Out)),!.
virtualize_code_each(_,_,In,Out):- must(Out=In).



map_compound_args(Pred,In,Out):- must(( compound(In), In=..[F|InL],maplist(Pred,InL,OutL),Out=..[F|OutL])).

map_compound_args(Pred,Args,In,Out):- must(( compound(Args), compound(In), Args=..[_|ArgsL],In=..[F|InL],maplist(Pred,ArgsL,InL,OutL),Out=..[F|OutL])).

could_safe_virtualize:- prolog_load_context(module,M),\+ clause_b(mtCycL(M)),
     \+ ((current_prolog_flag(dialect_pfc,true); 
       (source_location(F,_W),( atom_concat(_,'.pfc.pl',F);atom_concat(_,'.plmoo',F);atom_concat(_,'.pfc',F))))).

virtualize_source(X,In,Out):- (ground(In);true;current_prolog_flag(unsafe_speedups,true)),!,virtualize_code(X,In,Out).
virtualize_source(X,In,Out):- callable(In),term_variables(In,List),with_vars_locked(throw,List,virtualize_code(X,In,Out)).
  


%% safe_virtualize( Term, +How, -Wrapped) is semidet.
%
% Safely Paying Attention To Corner Cases Wrap.
%

safe_virtualize(Goal,How,Out):- must(safe_virtualize_0(Goal,How,call(MHow,MGoal))),!, 
   safe_univ(Out,[MHow,MGoal]).

safe_virtualize_0(M:Goal,M:How,call(How,M:Goal)).
safe_virtualize_0(M:Goal,How,call(How,M:Goal)).
safe_virtualize_0(Goal,baseKB:How,call(How,Goal)).
safe_virtualize_0(Goal,M:How,call(How,M:Goal)).
safe_virtualize_0(Goal,How,call(How,Goal)).

warn_if_static(F,A):- 
 ignore((F\={},
  functor(Goal,F,A),
  is_static_predicate(F/A),
  listing(Goal),
  trace_or_throw(warn(pfcPosTrigger,Goal,static)))).


%% decl_as(Types, TermM) is semidet.
%
% Declare as Types.
%
decl_as(Types,Var):-var(Var),!,trace_or_throw(var_decl_shared(Types,Var)).
decl_as(Types,M:FA):- if_defined(defaultAssertMt(M),fail),!,decl_as(Types,FA),!.
decl_as(Types,abox:FA):-!,decl_as(Types,FA),!.
decl_as(Types,_:M:G1):-!,decl_as(Types,M:G1),!.

decl_as(Types,(G1,G2)):-!,decl_as(Types,G1),!,decl_as(Types,G2),!.
decl_as(Types,[G1]):-!,decl_as(Types,G1),!.
decl_as(Types,[G1|G2]):-!,decl_as(Types,G1),!,decl_as(Types,G2),!.
decl_as(Types,M:(G1,G2)):-!,decl_as(Types,M:G1),!,decl_as(Types,M:G2),!.
decl_as(Types,M:[G1]):-!,decl_as(Types,M:G1),!.
decl_as(Types,M:[G1|G2]):-!,decl_as(Types,M:G1),!,decl_as(Types,M:G2),!.
decl_as(Types,M:F):-atom(F),!,decl_as(Types,M,F,_).
decl_as(Types,F):-atom(F),!,decl_as(Types,_,F,_).
decl_as(Types,M:F//Am2):-!,A is Am2+2, decl_as(Types,M,F,A).
decl_as(Types,M:F/A):-!,decl_as(Types,M,F,A).
decl_as(Types,F//Am2):-!,A is Am2+2, decl_as(Types,_,F,A).
decl_as(Types,F/A):-!,decl_as(Types,_,F,A).
decl_as(Types,M:Goal):-compound(Goal),!,functor(Goal,F,A),decl_as(Types,M,F,A).
decl_as(Types,Goal):-compound(Goal),!,functor(Goal,F,A),decl_as(Types,_,F,A).
decl_as(Types,Goal):-trace_or_throw(bad_decl_as(Types,Goal)).


decl_as(Types,M,F,A):- var(M),if_defined(defaultAssertMt(M),M=baseKB),!,decl_as(Types,M,F,A).
decl_as(Types,M,F,A):- var(A),!,forall(between(1,12,A),decl_as(Types,M,F,A)).
decl_as(M:Types,M,F,A):-!, decl_as(Types,M,F,A).
decl_as(Types,M,F,A):-!, decl_as_rev(M:F/A,Types).

decl_as_rev(MFA,(G1,G2)):-!,decl_as_rev(MFA,G1),!,decl_as_rev(MFA,G2),!.
decl_as_rev(MFA,[G1]):-!,decl_as_rev(MFA,G1),!.
decl_as_rev(MFA,[G1|G2]):-!,decl_as_rev(MFA,G1),!,decl_as_rev(MFA,G2),!.
decl_as_rev(MFA,M:(G1,G2)):-!,decl_as_rev(MFA,M:G1),!,decl_as_rev(MFA,M:G2),!.
decl_as_rev(MFA,M:[G1]):-!,decl_as_rev(MFA,M:G1),!.
decl_as_rev(MFA,M:[G1|G2]):-!,decl_as_rev(MFA,M:G1),!,decl_as_rev(MFA,M:G2),!.
decl_as_rev(M:F/A,Pred):- check_mfa(M,F,A),
  % wdmsg(call(M:Pred,M:F/A)),
  must(call(M:Pred,M:F/A)).

check_mfa(M,F,A):-sanity(atom(F)),sanity(integer(A)),sanity(current_module(M)).

kb_shared(SPEC):- decl_as('decl_kb_shared',SPEC),!.

:- multifile(baseKB:'already_decl_kb_shared'/3).
:- dynamic(baseKB:'already_decl_kb_shared'/3).

'decl_kb_shared'(M:F/A):- check_mfa(M,F,A),!,
  (baseKB:'already_decl_kb_shared'(M,F,A)->true;
  (asserta(baseKB:'already_decl_kb_shared'(M,F,A)),'do_decl_kb_shared'(M,F,A))),!.
'decl_kb_shared'(MFA):- trace_or_throw(bad_kb_shared(MFA)).

'do_decl_kb_shared'(M,prologSingleValued,0):- trace_or_throw('do_decl_kb_shared'(M,prologSingleValued,0)).
'do_decl_kb_shared'(M,F,A):-
 must_det_l((
  functor(PI,F,A),
  (is_static_predicate(M:PI) -> true ; (predicate_property(M:PI,dynamic) -> true ; on_xf_cont(M:dynamic(M:PI)))),
   decl_wrapped(M,F,A,ereq),
   baseKB:multifile(M:F/A),
   baseKB:export(M:F/A),
   system:import(M:F/A),
   system:export(M:F/A),
   baseKB:module_transparent(M:F/A), % in case this has clauses th
   baseKB:discontiguous(M:F/A),
   baseKB:public(M:F/A))).
   % on_f_throw( (M:F/A)\== (lmcache:loaded_external_kbs/1)),
   % (find_and_call(mtCycL(M))->ain(baseKB:prologHybrid(F));true),

decl_wrapped(M,F,A,How):-
 once((M==baseKB->true;ain(baseKB:predicateConventionMt(F,M)))),
 ain(baseKB:arity(F,A)),
 ain(baseKB:safe_wrap(F,A,How)).

% Skip Virtualizing
swc.

% Virtualize
vwc :- throw('Code was missed by virtualizer!').

% always goal expand (and remove it so it wont throw)
sd_goal_expansion(_,(VWC,In),Out):- vwc==VWC,!,callable(In),virtualize_source(ge,In,Out).
sd_goal_expansion(In,_,Out):- callable(In),    
   \+ current_prolog_flag(virtual_stubs,false),
   \+ (prolog_load_context(module,M),module_property(M,class(library))),
   virtualize_source(ge,In,Out).

%= 	 	 

%% same_terms( ?A, :TermB) is semidet.
%
% Same Terms.
%
same_terms(A,B):-A==B,!.
same_terms(A,B):-A=@=B,!,A=B.
same_terms(A,B):- A = B,!,fail.
same_terms((A:-AA),(B:-BB)):-!,same_terms(A,B),same_terms(AA,BB).
same_terms(M:A,B):-atom(M),!,same_terms(A,B).
same_terms(A,M:B):-atom(M),!,same_terms(A,B).

% nb_current('$goal_term',Was),Was==In,

should_base_sd(I):-  nb_current('$goal_term',Was),same_terms(I, Was),!,fail.
should_base_sd(I):-  
   (nb_current_or_nil('$source_term',TermWas),\+ same_terms(TermWas, I)),
   (nb_current_or_nil('$term',STermWas),\+ same_terms(STermWas, I)),!,
   fail.
should_base_sd(_).


:- ignore((source_location(S,_),prolog_load_context(module,M),module_property(M,class(library)),
 forall(source_file(M:H,S),
 ignore((functor(H,F,A),
  ignore(((\+ atom_concat('$',_,F),(export(F/A) , current_predicate(system:F/A)->true; system:import(M:F/A))))),
  ignore(((\+ predicate_property(M:H,transparent), module_transparent(M:F/A), \+ atom_concat('__aux',_,F),debug(modules,'~N:- module_transparent((~q)/~q).~n',[F,A]))))))))).

 
:-   dynamic(system:goal_expansion/4).
:- multifile(system:goal_expansion/4).
system:goal_expansion(In,Pos,Out,PosOut):- fail,
  \+ current_prolog_flag(xref,true),
  \+ current_prolog_flag(lm_expanders,false),  
  % \+ source_location(_,_),  
  current_prolog_flag(virtual_stubs,true),
  var(Pos),
  compound(In),strip_module(In,_,In0),compound(In0), 
  sd_goal_expansion(In,In0,Out)-> 
    (In\==Out,In0\==Out) -> 
      (dmsg(virtualize_goal(In)-->Out)) -> PosOut=Pos.


:-   dynamic(system:term_expansion/4).
:- multifile(system:term_expansion/4).
system:term_expansion((Head:-In),Pos,(Head:-Out),PosOut):- 
  \+ current_prolog_flag(xref,true),
  \+ current_prolog_flag(lm_expanders,false),  
  current_prolog_flag(virtual_stubs,true),
  nonvar(Pos),nb_current('$term',Head:-Goal),Goal==In,
  compound(In),strip_module(In,_,In0),compound(In0), 
  \+ ((prolog_load_context(module,M),module_property(M,class(library)))),
  sd_goal_expansion(In,In0,Out)-> 
    (In\==Out,In0\==Out) -> 
      (nop(dmsg(virtualize_body(In)-->(Head:-Out)))) -> PosOut=Pos.


/*
:- dynamic system:sub_call_expansion/2.
:- multifile system:sub_call_expansion/2.
:- dynamic system:sub_body_expansion/2.
:- multifile system:sub_body_expansion/2.
%system:term_expansion(X,Y):- compound(X),xform(X,Y).
%system:sub_body_expansion(In,Out):-virtualize_source(be,In,Out).
%system:sub_body_expansion(In,Out):- Out\== true, Out\=(cwc,_),could_safe_virtualize,virtualize_source(be,In,Out).
%system:sub_call_expansion(In,Out):-virtualize_source(ce,In,Out).
*/
