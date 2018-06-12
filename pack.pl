name(hook_hybrid).
version('1.1.118').
title('Hook assert retract call of *specific* predicates').
keywords([term_expansion,database,utility]).

author('Douglas R. Miles','logicmoo@gmail.com').
author('Douglas Miles', 'http://www.linkedin.com/in/logicmoo').
packager('TeamSPoon', 'https://github.com/TeamSPoon/').
maintainer('TeamSPoon', 'https://github.com/TeamSPoon/').
home('https://github.com/TeamSPoon/hook_hybrid.git').
download( 'https://github.com/TeamSPoon/hook_hybrid/release/*.zip').
requires(must_trace).
requires(loop_check).
requires(subclause_expansion).
requires(clause_attvars).
requires(file_scope).
requires(each_call_cleanup).

autoload(true).
