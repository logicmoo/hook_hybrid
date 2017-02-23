:- module(lockable_vars,[
   lock_vars/1,
   unlock_vars/1,
   with_vars_locked/2,
   with_vars_locked/3   
   ]).

:- set_module(class(library)).

:- use_module(library(dictoo)).


%% lock_vars( :TermVar) is semidet.
%
% Lock Variables.
%

lock_vars(Term):-lock_vars(lockable_vars:just_fail,Term).

just_fail(_):-fail.
skip_varlocks:- current_prolog_flag(unsafe_speedups , true) ,!.

:- meta_predicate(lock_vars(1,+)).
lock_vars(_Notify,Var):- (skip_varlocks; Var==[]),!.
%lock_vars(Notify,[Var]):- !, put_attr(Var,vl,when_rest(Notify,1,vv(Var))).
lock_vars(Notify,[Var|Vars]):- !, PVs=..[vv|[Var|Vars]], lock_these_vars_now(Notify,1,[Var|Vars],PVs),!.
lock_vars(Notify,Term):- term_variables(Term,Vs),lock_vars(Notify,Vs).

lock_these_vars_now(Notify,N0,[Var|Vars],PVs):-
   put_attr(Var,vl,when_rest(Notify,N0,PVs)), N is N0+1,
   lock_these_vars_now(Notify,N,Vars,PVs).
lock_these_vars_now(_,_,[],_).

%vl:attr_unify_hook(_,_):- \+ thread_self_main,!,fail.
vl:attr_unify_hook(when_rest(Notify,N,VVs),VarValue):- 
    arg(N,VVs,Was),N\==N,Was==VarValue,!,
    dmsg(collide_locked_var(Notify,VarValue)),
    call(Notify,VarValue).

vl:attr_unify_hook(when_rest(Notify,N,VVs),VarValue):- 
  \+ (var(VarValue);verbatum_var(VarValue)),!,
  dmsg(error_locked_var(when_rest(Notify,N,VVs),VarValue)),
  call(Notify,VarValue),!.

vl:attr_unify_hook(when_rest(Notify,N,VVs),VarValue):- 
      (get_attr(VarValue,vl,when_rest(Notify,N,VVs))
      -> true ; 
         put_attr(VarValue,vl,when_rest(Notify,N,VVs))).


%% unlock_vars( :TermOrVar) is semidet.
%
% Unlock Variables.
%

unlock_vars(_Var):- skip_varlocks,!.
unlock_vars(Term):- must(notrace((term_attvars(Term,Vs),maplist(delete_vl,Vs)))).

delete_vl( Var):- del_attr(Var,vl).

:- use_module(library(each_call_cleanup)).

:- meta_predicate(with_vars_locked(1,:)).
with_vars_locked(_Notify,Goal):- skip_varlocks,!,Goal.
with_vars_locked(Notify,Goal):- term_variables(Goal,Vs),
 each_call_cleanup(
   lock_vars(Notify,Vs),
      Goal,
     maplist(delete_vl,Vs)).

:- meta_predicate(with_vars_locked(1,?,:)).
with_vars_locked(_Notify,_Vs,Goal):- skip_varlocks,!,Goal.
with_vars_locked(Notify,Vs,Goal):-
 each_call_cleanup(
   lock_vars(Notify,Vs),
      Goal,
     maplist(delete_vl,Vs)).

