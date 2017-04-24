:- module(lockable_vars,[
   lock_vars/1,
   unlock_vars/1,
   with_vars_locked/2,
   with_vars_locked/3,
   with_vars_locked_trusted/3
   ]).

:- set_module(class(library)).



%% lock_vars( :TermVar) is semidet.
%
% Lock Variables.
%

lock_vars(Term):-lock_vars(lockable_vars:just_fail,Term).

just_fail(_):-fail.
skip_varlocks:- current_prolog_flag(unsafe_speedups , true) ,!.

:- meta_predicate(lock_vars(1,+)).
lock_vars(_Notify,Var):- (skip_varlocks; Var==[]),!.
%lock_vars(Notify,[Var]):- !, put_attr(Var,vl,when_rest(Notify,1,Var,vv(Var))).
lock_vars(Notify,[Var|Vars]):- !, PVs=..[vv|[Var|Vars]], lock_these_vars_now(Notify,1,[Var|Vars],PVs),!.
lock_vars(Notify,Term):- term_variables(Term,Vs),lock_vars(Notify,Vs).

lock_these_vars_now(Notify,N0,[Var|Vars],PVs):-!,
  ignore((var(Var),put_attr(Var,vl,when_rest(Notify,N0,Var,PVs)))), 
   N is N0+1,
   lock_these_vars_now(Notify,N,Vars,PVs).
lock_these_vars_now(_,_,[],_).


vl:attr_unify_hook(when_rest(Notify,N,_Var,VVs),VarValue):- 
    arg(N,VVs,Was),N\==N,Was==VarValue,!,
    dmsg(collide_locked_var(Notify,VarValue)),
    call(Notify,VarValue).

vl:attr_unify_hook(when_rest(_,_,Var,_),VarValue):- unify_name_based0(Var, VarValue).
vl:attr_unify_hook(_,VarValue):- verbatum_var(VarValue),!,variable_name_or_ref(VarValue,_),!.

vl:attr_unify_hook(_,_):- \+ thread_self_main,!,fail.
vl:attr_unify_hook(_,_):- thread_self_main,!.
vl:attr_unify_hook(when_rest(Notify,N,Var,VVs),VarValue):- 
  \+ (var(VarValue);verbatum_var(VarValue)),!,               
  dmsg(error_locked_var(when_rest(Notify,N,Var,VVs),VarValue)),
  call(Notify,VarValue),!.

vl:attr_unify_hook(when_rest(Notify,N,Var,VVs),VarValue):- var(VarValue),!,
      (get_attr(VarValue,vl,when_rest(Notify,N,Var,VVs))
      -> true ; 
         put_attr(VarValue,vl,when_rest(Notify,N,Var,VVs))).

vl:attr_unify_hook(_,VarValue):- verbatum_var(VarValue),!,variable_name_or_ref(VarValue,_),!.

:- thread_local(t_l:varname_lock/1).

unify_name_based0(Var1, Var2):- \+ atom(Var1),ger_var_name_or_ref(Var1,Name),!,unify_name_based0(Name, Var2).
unify_name_based0(Name1, Var):- if_defined(t_l:var_locked(What),fail),!,((get_var_name(Var,Name2),Name1==Name2)->true;call(What,Var)).
unify_name_based0(_Form, _OtherValue):- t_l:no_kif_var_coroutines(G),!,call(G).
unify_name_based0(Name1, Var):-  get_var_name(Var,Name2),!,Name1=Name2,!.
unify_name_based0(Name1, Var):- get_attr(Var, vn, Name2),!,combine_varnames(Name1,Name2,Name),(Name2==Name->true;put_attr(Var,vn,Name)).
unify_name_based0(Name1, Var):- var(Var),!,put_attr(Var, vn, Name1).
unify_name_based0(_, Var):- nonvar(Var),!.
%unify_name_based0(_, Var):- cyclic_term(Var),!,fail.
%unify_name_based0(_, Var):- cyclic_term(Var),!.
%unify_name_based0(_, Var):- cyclic_break(Var),!,fail.
unify_name_based0(_Form, _OtherValue):-!.

combine_varnames(Name1,Name2,Name1):-Name1==Name2,!.
combine_varnames(Name1,Name2,Name):-
 ((atom_concat(_,Name1,Name2);atom_concat(Name1,_,Name2)) -> Name=Name2 ; (
   ((atom_concat(Name2,_,Name1);atom_concat(_,Name2,Name1)) -> Name=Name1 ; (
   (atomic_list_concat([Name2,'_',Name1],Name)))))).


%% unlock_vars( :TermOrVar) is semidet.
%
% Unlock Variables.
%

unlock_vars(_Var):- skip_varlocks,!.
unlock_vars(Term):- must(notrace((term_attvars(Term,Vs),maplist(delete_vl,Vs)))).

delete_vl( Var):- var(Var),!, del_attr(Var,vl).
delete_vl( Term):- term_attvars(Term,Vs),maplist(delete_vl,Vs).

:- use_module(library(each_call_cleanup)).

:- meta_predicate(with_vars_locked(1,:)).
with_vars_locked(_Notify,Goal):- skip_varlocks,!,Goal.
with_vars_locked(Notify,Goal):- term_variables(Goal,Vs),with_vars_locked_trusted(Notify,Vs,Goal).

:- meta_predicate(with_vars_locked(1,?,:)).
with_vars_locked(_Notify,_Vs,Goal):- skip_varlocks,!,Goal.
with_vars_locked(Notify,Vs0,Goal):- term_variables(Vs0,Vs),with_vars_locked_trusted(Notify,Vs,Goal).

:- meta_predicate(with_vars_locked_trusted(1,?,:)).
with_vars_locked_trusted(Notify,Vs,Goal):-
 trusted_redo_call_cleanup(
   lock_vars(Notify,Vs),
      Goal,
     maplist(delete_vl,Vs)).

