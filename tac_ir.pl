:- dynamic t/1.
:- dynamic fp/1.
:- dynamic l/1.

t(0).
fp(0).
l(0).

%SECTION:helpers

tab :- write('\t').

readfile(In, X) :-
                    read(In, X).

put_label(X) :- write('l'), write(X), write(':'). 

get_labels(0, []).
get_labels(N, [L|Ls]) :- 
                    l(L), increment_l, N1 is N - 1,
                    get_labels(N1, Ls).  

increment_t :- t(X), Y is X + 1, asserta(t(Y)). 
increment_fp :- fp(X), Y is X + 1, asserta(fp(Y)). 
increment_l :- l(X), Y is X + 1, asserta(l(Y)). 

get_next_int_temp(X) :- t(X), increment_t.
get_next_real_temp(X) :- fp(X), increment_fp.
get_next_label(X) :- l(X), increment_l.

reset_t :- retractall(t(_)), assertz(t(0)).
reset_fp :- retractall(fp(_)), assertz(fp(0)).
reset_l :- retractall(l(_)), assertz(l(0)).

write_arg(bool, Val) :- write_arg(int, Val).
write_arg(int, Val) :- write('t'), write(Val).
write_arg(real, Val) :- write('fp'), write(Val).

write_args([]).
write_args([(Type, Val)]) :- write_arg(Type, Val).
write_args([(Type, Val)|Args]) :- 
                    write_arg(Type, Val), write(','),
                    write_args(Args).

process_expressions([], []).
process_expressions([Expr:Type|Exprs], [(Type, W)|X]) :-
                    ir_expr(Expr:Type, W), process_expressions(Exprs, X).

%ir related
%SECTION:store

ir_store(Id, bool, Kind, X) :- ir_store(Id, int, Kind, X).

ir_store(Id, int, local, X) :- 
                    tab, write('@'), write(Id),
                    write(' <- i_lstore t'),
                    write(X), nl.

ir_store(Id, int, arg, X) :- 
                    tab, write('@'), write(Id),
                    write(' <- i_astore t'),
                    write(X), nl.

ir_store(Id, int, var, X) :- 
                    tab, write('@'), write(Id),
                    write(' <- i_gstore t'),
                    write(X), nl.

ir_store(Id, real, local, X) :- 
                    tab, write('@'), write(Id),
                    write(' <- r_lstore fp'),
                    write(X), nl.

ir_store(Id, real, arg, X) :- 
                    tab, write('@'), write(Id),
                    write(' <- r_astore fp'),
                    write(X), nl.

ir_store(Id, real, var, X) :-
                    tab, write('@'), write(Id),
                    write(' <- r_gstore fp'),
                    write(X), nl.

%SECTION:load

ir_load(Id, bool, Kind, X) :- ir_load(Id, int, Kind, X).

ir_load(Id, int, local, X) :- 
                    tab, write('t'), get_next_int_temp(X), 
                    write(X), write(' <- i_lload @'), write(Id),
                    nl.

ir_load(Id, int, arg, X) :- 
                    tab, write('t'), get_next_int_temp(X),
                    write(X), write(' <- i_aload @'), write(Id),
                    nl.

ir_load(Id, int, var, X) :- 
                    tab, write('t'), get_next_int_temp(X), 
                    write(X), write(' <- i_gload @'), write(Id),
                    nl.

ir_load(Id, real, local, X) :-
                    tab, write('fp'), get_next_real_temp(X), 
                    write(X), write(' <- r_lload @'), write(Id),
                    nl.

ir_load(Id, real, arg, X) :-
                    tab, write('fp'), get_next_real_temp(X), 
                    write(X), write(' <- r_aload @'), write(Id),
                    nl.

ir_load(Id, real, var, X) :- 
                    tab, write('fp'), get_next_real_temp(X), 
                    write(X), write(' <- r_gload @'), write(Id),
                    nl.

ir_value(Val, int, X) :- 
                    tab, write('t'), get_next_int_temp(X),
                    write(X), write(' <- i_value '),
                    write(Val), nl.

ir_value(Val, real, X) :- 
                    tab, write('fp'), get_next_real_temp(X),
                    write(X), write(' <- r_value '),
                    write(Val), nl.

%SECTION:arithm

ir_mul(int, T1, T2, X) :- 
                    get_next_int_temp(X), tab, write('t'),
                    write(X), write(' <- i_mul t'),
                    write(T1), write(', t'),
                    write(T2), nl.

ir_mul(real, F1, F2, X) :-
                    get_next_real_temp(X), tab, write('fp'), 
                    write(X), write(' <- r_mul fp'),
                    write(F1), write(', fp'),
                    write(F2), nl.

ir_div(int, T1, T2, X) :-
                    get_next_int_temp(X), tab, write('t'), 
                    write(X),
                    write(' <- i_div t'), write(T1),
                    write(', t'), write(T2), nl.

ir_div(real, F1, F2, X) :- 
                    get_next_real_temp(X), tab, write('fp'),
                    write(X),
                    write(' <- r_div fp'), write(F1),
                    write(', fp'), write(F2), nl.

ir_add(int, T1, T2, X) :- 
                    get_next_int_temp(X), tab, write('t'), write(X),
                    write(' <- i_add t'), write(T1),
                    write(', t'), write(T2), nl.

ir_add(real, F1, F2, X) :-
                    get_next_real_temp(X), tab, write('fp'), write(X),
                    write(' <- r_add fp'), write(F1),
                    write(', fp'), write(F2), nl.

ir_sub(int, T1, T2, X) :-
                    get_next_int_temp(X), tab, write('t'), write(X),
                    write(' <- i_sub t'), write(T1),
                    write(', t'), write(T2), nl.

ir_sub(real, F1, F2, X) :-
                    get_next_real_temp(X), tab, write('fp'), write(X),
                    write(' <- r_sub fp'), write(F1),
                    write(', fp'), write(F2), nl.

ir_mod(int, T1, T2, X) :- 
                    get_next_int_temp(X), tab, write('t'), write(X),
                    write(' <- mod t'), write(T1),
                    write(', t'), write(T2),
                    nl.

ir_inv(int, T1, X) :-
                    get_next_int_temp(X), tab, write('t'), write(X),
                    write(' <- i_inv t'), write(T1), 
                    nl.

ir_inv(real, F1, X) :- 
                    get_next_int_temp(X), tab, write('fp'), write(X),
                    write(' <- r_inv fp'), write(F1), 
                    nl.

%SECTION:logic 

ir_lt(int, T1, T2, X) :-
                    get_next_int_temp(X), tab, write('t'), write(X),
                    write(' <- i_lt t'), write(T1),
                    write(', t'), write(T2), nl.

ir_lt(real, F1, F2, X) :- 
                    get_next_int_temp(X), tab, write('t'), write(X),
                    write(' <- r_lt fp'), write(F1),
                    write(', fp'), write(F2), nl.

ir_gt(Type, V1, V2, X) :- ir_lt(Type, V2, V1, X).

ir_eq(int, T1, T2, X) :- 
                    get_next_int_temp(X), tab, write('t'), write(X),
                    write(' <- i_eq t'), write(T1),
                    write(', t'), write(T2), nl.

ir_eq(real, F1, F2, X) :- 
                    get_next_int_temp(X), tab, write('t'), write(X),
                    write(' <- r_eq fp'), write(F1),
                    write(', fp'), write(F2), nl.

ir_ne(int, T1, T2, X) :- 
                    get_next_int_temp(X), tab, write('t'), write(X),
                    write(' <- i_ne t'), write(T1),
                    write(', t'), write(T2), nl.

ir_ne(real, F1, F2, X) :- 
                    get_next_int_temp(X), tab, write('t'), write(X),
                    write(' <- r_ne fp'), write(F1),
                    write(', fp'), write(F2), nl.

ir_le(int, T1, T2, X) :- 
                    get_next_int_temp(X), tab, write('t'), write(X),
                    write(' <- i_le t'), write(T1),
                    write(', t'), write(T2), nl.

ir_le(real, F1, F2, X) :- 
                    get_next_int_temp(X), tab, write('t'), write(X),
                    write(' <- r_le fp'), write(F1),
                    write(', fp'), write(F2), nl.

ir_ge(Type, V1, V2, X) :- ir_le(Type, V2, V1, X).

ir_not(bool, T1, X) :- 
                    get_next_int_temp(X), tab, write('t'), write(X),
                    write(' <- i_not t'), write(T1), nl.

%SECTION:coersion

ir_toreal(X, Y) :- 
                    tab, write('fp'), get_next_real_temp(Y),
                    write(Y), write(' <- itor t'),
                    write(X), nl.

%SECTION:copy

ir_copy(int, T1, T2) :- 
                    tab, write('t'), write(T1), 
                    write(' <- i_copy t'), write(T2),
                    nl.

ir_copy(real, F1, F2) :- 
                    tab, write('fp'), write(F1),
                    write(' <- r_copy fp'), write(F2),
                    nl.

%SECTION:jump

ir_cjump(X, L1, L2) :-
                    tab, write('cjump t'), write(X),
                    write(', l'), write(L1), write(' ,l'),
                    write(L2), nl.

ir_jump(L) :- tab, write('jump l'), write(L), nl.

%SECTION:calls


ir_call(bool, Id, Args, X) :- ir_call(int, Id, Args, X).

ir_call(int, Id, Args, X) :- 
                    tab, get_next_int_temp(X), write('t'), 
                    write(X), write(' <- i_call @'), write(Id),
                    write(', ['), write_args(Args), write(']'), nl.

ir_call(real, Id, Args, X) :- 
                    tab, get_next_real_temp(X), write('fp'),
                    write(X), write(' <- r_call @'), write(Id),
                    write(', ['), write_args(Args), write(']'), nl.

ir_call(nil, Id, Args) :-
                    tab, write('call @'), write(Id),
                    write(', ['), write_args(Args), write(']'), nl.

%SECTION:logic expressions

ir_expr(or(Expression1, Expression2) : bool, X) :- 
                    get_labels(2, [L1, L2]), ir_expr(Expression1, X),
                    ir_cjump(X, L1, L2), put_label(L2),
                    ir_expr(Expression2, Y), ir_copy(int, X, Y),
                    put_label(L1).
     
ir_expr(and(Expression1, Expression2) : bool, X) :-
                    get_labels(2, [L1, L2]), ir_expr(Expression1, X),
                    ir_cjump(X, L1, L2), put_label(L1),
                    ir_expr(Expression2, Y), ir_copy(int, X, Y), 
                    put_label(L2).

ir_expr(eq(Expression1:Type, Expression2:Type) : bool, Z) :- 
                    ir_expr(Expression1:Type, X),
                    ir_expr(Expression2:Type, Y), ir_eq(Type, X, Y, Z).

ir_expr(ne(Expression1:Type, Expression2:Type) : bool, Z) :- 
                    ir_expr(Expression1:Type, X), 
                    ir_expr(Expression2:Type, Y), ir_ne(Type, X, Y, Z).

ir_expr(lt(Expression1:Type, Expression2:Type) : bool, Z) :- 
                    ir_expr(Expression1:Type, X),
                    ir_expr(Expression2:Type, Y), ir_lt(Type, X, Y, Z).

ir_expr(le(Expression1, Expression2) : bool, Z) :- 
                    ir_expr(Expression1:Type, X),
                    ir_expr(Expression2:Type, Y), ir_le(Type, X, Y, Z).

ir_expr(gt(Expression1:Type, Expression2:Type) : bool, Z) :-
                    ir_expr(Expression1:Type, X), 
                    ir_expr(Expression2:Type, Y), ir_gt(Type, X, Y, Z).

ir_expr(ge(Expression1:Type, Expression2:Type) : bool, Z) :- 
                    ir_expr(Expression1:Type, X),
                    ir_expr(Expression2:Type, Y), ir_ge(Type, X, Y, Z).

ir_expr(not(Expression1:Type) : bool, Z) :- 
                    ir_expr(Expression1:Type, X), ir_not(Type, X, Z).

%SECTION:arithm expressions

ir_expr(plus(Expression1, Expression2) : Type, Z) :- 
                    ir_expr(Expression1, X),
                    ir_expr(Expression2, Y), ir_add(Type, X, Y, Z).

ir_expr(minus(Expression1, Expression2) : Type, Z):- 
                    ir_expr(Expression1, X),
                    ir_expr(Expression2, Y), ir_sub(Type, X, Y, Z).

ir_expr(times(Expression1, Expression2):Type, Z) :- 
                    ir_expr(Expression1, X),
                    ir_expr(Expression2, Y), ir_mul(Type, X, Y, Z).

ir_expr(div(Expression1, Expression2) : Type, Z) :- 
                    ir_expr(Expression1, X),
                    ir_expr(Expression2, Y), ir_div(Type, X, Y, Z).

ir_expr(mod(Expression1, Expression2) : int, Z) :- 
                    ir_expr(Expression1, X),
                    ir_expr(Expression2, Y), ir_mod(int, X, Y, Z).

ir_expr(inv(Expression1) : Type, Z) :- 
                    ir_expr(Expression1, X),
                    ir_inv(Type, X, Z).

%atomic 

ir_expr(int_literal(Val): int, X) :- ir_value(Val, int, X).
ir_expr(real_literal(Val): real, X) :- ir_value(Val, real, X).

ir_expr(true : bool, X) :- ir_value(1, int, X).
ir_expr(false : bool, X) :- ir_value(0, int, X).

ir_expr(id(Id, Kind, Type): Type, X) :- ir_load(Id, Type, Kind, X).

ir_expr(toreal(Expression) : real, Y) :- 
                    ir_expr(Expression, X),
                    ir_toreal(X, Y).

ir_expr(call(Id, Expressions):Type, Z) :- 
                    process_expressions(Expressions, X),
                    ir_call(Type, Id, X, Z).

%SECTION:io procedures

ir_print(bool, B1) :- 
                    tab, write('b_print t'),
                    write(B1), nl. 

ir_print(int, T1) :- 
                    tab, write('i_print t'),
                    write(T1), nl.

ir_print(real, F1) :-
                    tab, write('r_print fp'),
                    write(F1), nl.

ir_read(bool, X) :- 
                    tab, get_next_int_temp(X), write('t'),
                    write(X), write(' <- b_read'), nl.

ir_read(int, X) :- 
                    tab, get_next_int_temp(X), write('t'),
                    write(X), write(' <- i_read'), nl.

ir_read(real, X) :- 
                    tab, get_next_real_temp(X), write('fp'),
                    write(X), write(' <- r_read'), nl.

%statements 

ir_s_statement(assign(id(Id, Kind, Type), Expression)) :- 
                    ir_expr(Expression, X), ir_store(Id, Type, Kind, X).

ir_s_statement(while(Expression, Statement)) :- 
                    get_labels(3, [L1, L2, L3]),  put_label(L1), ir_expr(Expression, X),
                    ir_cjump(X, L2, L3), 
                    put_label(L2), ir_statement(Statement), ir_jump(L1), put_label(L3).

ir_s_statement(if(Expression, Statement1, nil)) :-
                    get_labels(2, [L1, L2]), ir_expr(Expression, X),
                    ir_cjump(X, L1, L2),
                    put_label(L1), ir_statement(Statement1), put_label(L2).

ir_s_statement(if(Expression, Statement1, Statement2)) :- 
                    get_labels(3, [L1, L2, L3]), ir_expr(Expression, X),
                    ir_cjump(X, L1, L2),
                    put_label(L1), ir_statement(Statement1),
                    ir_jump(L3), put_label(L2),
                    ir_statement(Statement2), put_label(L3).

ir_s_statement(print(Expression:Type)) :- 
                    ir_expr(Expression:Type, X), 
                    ir_print(Type, X). 

ir_s_statement(read(id(Id, Kind, Type))) :- ir_read(Type, X), ir_store(Id, Type, Kind, X).

ir_s_statement(call(Id, Expressions)) :- 
                    process_expressions(Expressions, X), ir_call(nil, Id, X).

ir_statement([]).
ir_statement(S) :- ir_s_statement(S).
ir_statement([S|Ss]) :- ir_s_statement(S), ir_statement(Ss).

%SECTION:function related

write_fun_name(Id) :- write('function @'), write(Id), nl.

ir_process_fun_body(body([], nil, Expression)) :- 
                    ir_process_ret_expression(Expression).

ir_process_fun_body(body(Declarations, Statement, Expression)) :- 
                    ir_process_declarations(Declarations),
                    ir_process_statement(Statement), ir_process_ret_expression(Expression).

ir_process_declarations([]).
ir_process_declarations([D|Ds]) :- ir_declaration(D), ir_process_declarations(Ds).

ir_declaration(local(_, _, nil)).
ir_declaration(local(Id, Type, Expression)) :- ir_expr(Expression, X), ir_store(Id, Type, local, X).

ir_process_statement(Statement) :- ir_statement(Statement).

ir_process_ret_expression(nil) :- ir_return(nil).
ir_process_ret_expression(Expression:Type) :- ir_expr(Expression:Type, X), ir_return(Type, X).

ir_return(nil) :- tab, write('return'), nl.

ir_return(bool, X) :- ir_return(int, X).
ir_return(int, X) :- tab, write('i_return t'), write(X), nl.
ir_return(real, X) :- tab, write('r_return fp'), write(X), nl.

%SECTION:ast related

ir_ast_process(var(_, _)).
ir_ast_process(fun(Identifier, _, Body)) :- 
                    write_fun_name(Identifier), ir_process_fun_body(Body),
                    reset_fp, reset_t.

ir_ast_list_process([]).
ir_ast_list_process([AST|ASTs]) :- ir_ast_process(AST), nl, !, ir_ast_list_process(ASTs).

read_terms(_, end_of_file, []).
read_terms(In, X, [X|Y]) :- read(In, Z), read_terms(In, Z, Y).
read_terms(In, Y) :- read(In, X), read_terms(In, X, Y).

start(Name) :- reset_t, reset_fp, reset_l, open(Name, read, In), read_terms(In, X), close(In), ir_ast_list_process(X), !.
