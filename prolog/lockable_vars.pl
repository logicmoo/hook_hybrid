:- module(lockable_vars,[
   with_local_vars_locked/2,
   with_local_vars_locked/3
   ]).

:- meta_predicate dual_notify(1,1,?).


%% lock_local_vars( :TermVar) is semidet.
%
% Lock Variables.
%

lock_local_vars(Term):-lock_local_vars(fail,Term).

lock_local_vars( _Notify, _Term):-!.
lock_local_vars(_Notify,_Var):-  current_prolog_flag(unsafe_speedups , true) ,!.
lock_local_vars( Notify, Term):-  must(notrace((NotifyP=call(Notify),term_variables(Term,Vs),maplist(lock_each_local_var(NotifyP,Vs),Vs)))).

lock_each_local_var(Notify,Vs,Var):- get_attr(Var,vll,when_rest(NotifyP,RestP)),delete_eq(Vs,Var,Rest),
   append(Rest,RestP,NewRest),put_attr(Var,vll,when_rest(dual_notify(Notify,NotifyP),NewRest)).
lock_each_local_var(Notify,Vs,Var):- delete_eq(Vs,Var,Rest),put_attr(Var,vll,when_rest(Notify,Rest)).
% lock_each_local_var(_,_ ,  Var):-var(Var),!,only_stars(Var).

dual_notify(N1,N2,Value):-ignore( \+ call(N1,Value)),ignore( \+ call(N2,Value)).

%vll:attr_unify_hook(_,_):- \+ thread_self_main,!,fail.
vll:attr_unify_hook(when_rest(Notify,RestOfVars),VarValue):-
  not_member_eq(VarValue,RestOfVars),
  \+ (var(VarValue);verbatum_var(VarValue)),
  nb_setarg(1,Notify,wdmsg),
 /* dumpST,
  dmsg(error_locked_var(Notify,VarValue)),!,
  dtrace,*/
  dmsg(error_locked_var(Notify,VarValue)),
  call(Notify,VarValue),!.
vll:attr_unify_hook(_,_).


%% unlock_local_vars( :TermVar) is semidet.
%
% Unlock Variables.
%

%unlock_local_vars(_Var):- current_prolog_flag(unsafe_speedups , true) ,!.
unlock_local_vars( Var):- attvar(Var),!,del_attr(Var,vll).
unlock_local_vars(Term):- must(notrace((term_attvars(Term,Vs),maplist(unlock_local_vars,Vs)))).

:- use_module(library(each_call_cleanup)).

:- meta_predicate(with_local_vars_locked(1,0)).
with_local_vars_locked(Notify,Goal):- term_variables(Goal,Vs),with_local_vars_locked(Notify,Vs,Goal).

:- meta_predicate(with_local_vars_locked(1,?,0)).
with_local_vars_locked(_Notify,_Vs,_Goal):- \+ thread_self(main),!.
with_local_vars_locked(Notify,Vs,Goal):-
 each_call_cleanup(
   lock_local_vars(Notify,Vs),
      Goal,
     unlock_local_vars(Vs)).

