name(hook_hybrid).
version('1.1.112').
title('Hook assert retract call of *specific* predicates').
keywords([term_expansion,database,utility]).

author('Douglas R. Miles','logicmoo@gmail.com').
author('Douglas Miles', 'http://www.linkedin.com/in/logicmoo').
packager('TeamSPoon', 'https://github.com/TeamSPoon/').
maintainer('TeamSPoon', 'https://github.com/TeamSPoon/').
home('https://github.com/TeamSPoon/prologmud.git').
download( 'https://github.com/TeamSPoon/prologmud/release/*.zip').
requires(must_trace).
requires(loop_check).
requires(subclause_expansion).
requires(clause_attvars).
requires(file_scope).
requires(each_call_cleanup).
autoload(true).
