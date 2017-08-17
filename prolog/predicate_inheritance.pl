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
:- module(predicate_inheritance,
          [
check_mfa/4,
%skip_mfa/4,
create_predicate_inheritance/3,
create_predicate_inheritance_0/3,
decl_as/2,
decl_kb_shared/1,
decl_kb_local/1,
do_import/4,
kb_local/1,
(kb_shared)/1,
(kb_local)/1,
(kb_global)/1,
make_as_dynamic/4
]).

:- set_module(class(library)).
:- reexport(library(must_trace)).
:- reexport(library(loop_check)).

:- meta_predicate decl_as(1,+).
:- meta_predicate decl_as_rev(+,+).


:- if( \+ current_op(_,_,(kb_shared))).

:- current_prolog_flag(access_level,Was),
   set_prolog_flag(access_level,system),
   op(1150,fx,(kb_shared)),
   op(1150,fx,(kb_global)),
   op(1150,fx,(kb_local)),
   set_prolog_flag(access_level,Was).

:- endif.


:- module_transparent((
check_mfa/4, 
%skip_mfa/4,
create_predicate_inheritance/3,
create_predicate_inheritance_0/3,
decl_as/2,
do_import/4,
(kb_shared)/1,
(kb_local)/1,
(kb_global)/1,
make_as_dynamic/4
          )).



%% create_predicate_inheritance_0(+ChildDefMt,+F,+A) is semidet.
%
% Ensure inherit_above/2 stub is present in ChildDefMt.
%

create_predicate_inheritance(CallerMt,F,A):-
  create_predicate_inheritance_0(CallerMt,F,A),!.
create_predicate_inheritance_0(Nonvar,F,A):- var(Nonvar)-> break ; (sanity(ground(create_predicate_inheritance_0(Nonvar,F,A))),fail).
% TODO unsuspect the next line (nothing needs to see above baseKB)


create_predicate_inheritance_0(baseKB,F,A):- !, make_as_dynamic(baseKB,F,A).
/*
create_predicate_inheritance_0(baseKB,F,A):- !,
  make_as_dynamic(create_predicate_inheritance_0(baseKB,F,A),baseKB,F,A), 
     ignore((( \+ (defaultAssertMt(CallerMt),CallerMt\==baseKB,create_predicate_inheritance_0(CallerMt,F,A) )))).
*/

create_predicate_inheritance_0(abox,F,A):-  
       !, must(defaultAssertMt(CallerMt)),
       sanity(CallerMt\=abox),!,
       create_predicate_inheritance_0(CallerMt,F,A).

create_predicate_inheritance_0(CallerMt,F,A):- fail, clause_b(mtProlog(CallerMt)),
   sanity(\+ clause_b(mtHybrid(CallerMt))),!,
   wdmsg(warn(create_predicate_istAbove_mtProlog(CallerMt,F,A))),dtrace.

create_predicate_inheritance_0(CallerMt,F,A):- 
  lmcache:already_decl(kb_global,M,F,A),do_import(CallerMt,M,F,A),!.

create_predicate_inheritance_0(CallerMt,F,A):-
   make_as_dynamic(create_predicate_inheritance_0(CallerMt,F,A),CallerMt,F,A),
   functor(Goal,F,A),
   CallerMt:import(inherit_above/2),
   CallerMt:import(do_ihherit_above/2),
   CallerMt:assert_if_new(( CallerMt:Goal :- inherit_above(CallerMt,Goal))).

:- module_transparent(system:inherit_above/2).
:- export(system:inherit_above/2).
system:inherit_above(Mt,Query):-  
   \+ context_module(baseKB), 
   Query\=do_inherit_above(_,_),
   do_inherit_above(Mt,Query).

never_move(spft,_).
never_move(mpred_prop,_).
never_move(meta_argtypes,_).
never_move(pt,_).
never_move(bt,_).
never_move(nt,_).
:- module_transparent(system:do_inherit_above/2).
:- export(system:do_inherit_above/2).
system:do_inherit_above(Mt,QueryIn):- 
   functor(QueryIn,F,A),\+ never_move(F,A),
   predicate_property(QueryIn,number_of_clauses(N)),
   Mt:nth_clause(QueryIn,N,Ref),clause(_,Body,Ref),
   Body\=inherit_above(Mt,QueryIn),
   once((Mt:clause(QueryIn,inherit_above(Mt,_),Kill),
   erase(Kill),functor(Query,F,A),
   dmsg(moving(inherit_above(Mt,Query))),
   Mt:assertz((Query:-inherit_above(Mt,Query))))),fail.

  % TODO   no_repeats(MtAbove,(clause(Mt:genlMt(Mt,MtAbove),true);clause(baseKB:genlMt(Mt,MtAbove),true))),
system:do_inherit_above(Mt,Query):- 
   clause(baseKB:genlMt(Mt,MtAbove),true),
   MtAbove:Query.



make_as_dynamic(M,F,A):- make_as_dynamic(make_as_dynamic,M,F,A).

make_as_dynamic(Reason,M,F,A):-
 must_det_l((
   functor(PI,F,A),
   M:multifile(M:F/A),
   M:discontiguous(M:F/A),
   M:module_transparent(M:F/A),
   (is_static_predicate(M:PI) -> true ; (predicate_property(M:PI,dynamic) -> true ; must(M:dynamic(M:PI)))),   
   public(M:F/A),
   nop(on_f_throw( (M:F/A)\== (baseKB:loaded_external_kbs/1))),
   nop(assertz_if_new(( M:PI :- (fail,infoF(createdFor(Reason)))))))).


do_inherit(_SM,_M,_F,_A).

% TODO uncomment these out!
%do_import(system,M,F,A):-throw(unexpected(do_import(system,M,F,A))).
%do_import(user,M,F,A):-throw(unexpected(do_import(user,M,F,A))).
do_import(TM,M,F,A):- 
   must((TM:import(M:F/A),TM:export(TM:F/A))),!.
   % must((TM:module_transparent(M:F/A))). % in case this has clauses th

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
decl_as_rev(M:F/A,OM:Pred):- check_mfa(OM:Pred,OM,F,A),
  must(call(OM:Pred,M:F/A)),!.
decl_as_rev(M:F/A,Pred):- check_mfa(Pred,M,F,A),
  must(call(M:Pred,M:F/A)).











% skip_mfa(Why,M, genlMt, 2):- baseKB\=M,dumpST,dmsg(skip_mfa(Why,M, genlMt, 2)),!,break.
check_mfa(_Why,M,F,A):-sanity(atom(F)),sanity(integer(A)),sanity(current_module(M)).



kb_shared(SPEC):- SPEC=(_:_), !, decl_as(decl_kb_local,SPEC), context_module(M),!,( \+ mtHybrid(M) -> M:import(SPEC); true).
kb_shared(SPEC):- decl_as(decl_kb_local,SPEC),!.

kb_global(SPEC):- SPEC=(_:_), !, decl_as(decl_kb_shared,SPEC),!,import(SPEC).
kb_global(SPEC):- dumpST,break,decl_as(decl_kb_shared,SPEC),!,import(SPEC).

:- multifile(lmcache:already_decl/4).
:- dynamic(lmcache:already_decl/4).
predicate_m_f_a_decl(M,F,A,Other):- lmcache:already_decl(Other,M,F,A).

% TODO comment this out!
decl_kb_shared(M:'==>'/A):- !, dmsg(skip(decl_kb_shared(M:'==>'/A))).

decl_kb_shared(M:F/A):- check_mfa(kb_global,M,F,A),!,
  (lmcache:already_decl(kb_global,M,F,A)->true;
  (asserta(lmcache:already_decl(kb_global,M,F,A)),do_decl_kb_shared(M,F,A))),!.
decl_kb_shared(MFA):- trace_or_throw(bad_kb_shared(MFA)).

do_decl_kb_shared(M,prologSingleValued,0):- trace_or_throw(do_decl_kb_shared(M,prologSingleValued,0)).

do_decl_kb_shared(M,F,A):-functor(PI,F,A),do_decl_kb_shared_1(M,F,A,PI).

%do_decl_kb_shared_1(M,F,A,PI):- M\=baseKB,M\=elmt,M\=rdf_rewrite,\+ clause(baseKB:using_pfc(user,M,pfc_mod),true),dumpST,break,(trace_or_throw(do_decl_kb_shared_m(M,F,A,PI))).
%do_decl_kb_shared_1(M,F,A,PI):- if_defined(mpred_database_term(F,A,_),F = ~),dmsg(trace_or_throw(do_decl_kb_shared_1(M,F,A,PI))).
do_decl_kb_shared_1(M,F,A,PI):- lmcache:already_decl(Other,M,F,A), Other \== (kb_global), dmsg(warn(trace_or_throw(already_decl(Other,M,F,A,PI)))),!.

do_decl_kb_shared_1(M,F,A,PI):- \+ predicate_property(M:PI,imported_from(_)), predicate_property(M:PI,defined),!,do_decl_kb_shared_2(M,F,A,PI).
% not possible do_decl_kb_shared_1(M,F,A,PI):- predicate_property(M:PI,imported_from(M)),!,do_decl_kb_shared_2(M,F,A,PI).

do_decl_kb_shared_1(M,F,A,PI):- predicate_property(M:PI,imported_from(R)),R\==M,!,
   show_call(pfc(inherited_shared(R)),do_import(M,R,F,A)),
   do_decl_kb_shared_2(R,F,A,PI),
   nop(do_import(system,R,F,A)),!.

do_decl_kb_shared_1(M,F,A,PI):- current_predicate(F,R:PI), 
   \+ predicate_property(R:PI,inherited_from(_)),
   R\==M,
   dmsg(pfc(shared_found_peer(R,M:F/A))),
   do_import(M,R,F,A),
   do_decl_kb_shared_2(R,F,A,PI),
   nop(do_import(system,R,F,A)),!.

do_decl_kb_shared_1(M,F,A,PI):- do_decl_kb_shared_2(M,F,A,PI),!.
  

do_decl_kb_shared_2(M,F,A,_PI):- 
   nop(dmsg((do_decl_kb_shared(M,F,A)))),
 must_det_l((
   make_as_dynamic(kb_global(M:F/A),M,F,A),
    M:export(M:F/A),
    do_import(baseKB,M,F,A),
    do_import(pfc_toplevel,M,F,A),   
    do_import(pfc_mod,M,F,A),   
    do_import(pfc_lib,M,F,A),   
    do_import(mpred_type_isa,M,F,A),

   do_import(system,M,F,A),   
% TODO BEGIN comment these out!
   do_import(user,M,F,A),
   %do_import(header_sane,M,F,A),      
   %'$current_source_module'(SM),do_import(SM,M,F,A),   
   %'$current_typein_module'(TM),do_import(TM,M,F,A),
% TODO END comment these out!
   decl_wrapped(M,F,A,ereq))).

   % on_f_throw( (M:F/A)\== (lmcache:loaded_external_kbs/1)),
   % (find_and_call(mtHybrid(M))->ain(baseKB:prologHybrid(F));true),


% kb_local(SPEC):- !,kb_global(SPEC),!.


kb_local(M:F/A):- lmcache:already_decl(kb_global,R,F,A), 
   dmsg(warn(kb_local(already_decl(kb_global,R->M,F,A)))),!.
kb_local(R:F/A):- lmcache:already_decl(kb_global,M,F,A),!,do_import(M,R,F,A).

kb_local(SPEC):- decl_as(decl_kb_local,SPEC),!.

decl_kb_local(M:'==>'/A):- A==1, !, nop(dmsg(skip(decl_kb_local(M:'==>'/A)))).

decl_kb_local(M:F/A):- lmcache:already_decl(kb_global,R,F,A), 
   dmsg(warn(trace_or_throw(already_decl(kb_global,R->M,F,A)))),!.

decl_kb_local(M:F/A):- check_mfa(kb_local,M,F,A),!,
  (lmcache:already_decl(kb_local,M,F,A)->true;
    (asserta(lmcache:already_decl(kb_local,M,F,A)),do_decl_kb_local(M,F,A))),!.
decl_kb_local(MFA):- trace_or_throw(bad_kb_local(MFA)).

do_decl_kb_local(M,prologSingleValued,0):- trace_or_throw(do_decl_kb_local(M,prologSingleValued,0)).

do_decl_kb_local(M,F,A):-functor(PI,F,A),do_decl_kb_local_1(M,F,A,PI),!.

do_decl_kb_local_1(M,F,A,_):- lmcache:already_decl(Other,M,F,A),Other\=(kb_local),!. % ,dmsg(lmcache:already_decl(kb_global,M,F,A)).

do_decl_kb_local_1(M,F,A,PI):-
  predicate_property(M:PI,inherited_from(R)),R\==M,!,
  do_decl_kb_local_2(R,F,A,PI),
  show_call(pfc(inherited_local(R)),do_import(M,R,F,A)).

do_decl_kb_local_1(M,F,A,PI):- 
  % \+ predicate_property(M:PI,inherited_from(_)), 
  predicate_property(M:PI,defined),
  do_decl_kb_local_2(M,F,A,PI).
% not possible do_decl_kb_local_1(M,F,A,PI):- predicate_property(M:PI,inherited_from(M)),!,do_decl_kb_local_2(M,F,A,PI).

do_decl_kb_local_1(M,F,A,PI):- fail,
   findall(R,(current_predicate(F,R:PI), 
   \+ predicate_property(R:PI,inherited_from(_)),
   R\==M),Rs),Rs\==[],Rs\==[baseKB],
   dmsg(pfc(local_found_peer(Rs,M:F/A))),fail,
   !,
   show_call(pfc(found_peer(R)),do_import(M,R,F,A)).

do_decl_kb_local_1(M,F,A,PI):- do_decl_kb_local_2(M,F,A,PI),!.
  

do_decl_kb_local_2(M,F,A,_PI):- 
 nop(dmsg((do_decl_kb_local(M,F,A)))),
 must_det_l((
  make_as_dynamic(kb_local(M:F/A),M,F,A),
  create_predicate_inheritance_0(M,F,A),
  decl_wrapped(M,F,A,ereq))).



