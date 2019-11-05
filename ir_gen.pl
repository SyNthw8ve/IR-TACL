:- dynamic t/1.
:- dynamic fp/1.
:- dynamic l/1.

t(0).
fp(0).
l(0).

%SECTION:helpers

tab :- tab(4).

readfile(Name, X) :-
                    open(Name, read, In), read_term(In, X, []),
                    close(In).

save(X, bool, Z) :- save(X, int, Z).

save(X, int, Z) :- 
                    t(W), Y is W - 1, append(X, [(int, Y)], Z).

save(X, real, Z) :- 
                    fp(W), Y is W - 1, append(X, [(real, Y)], Z).

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

last_get_next_int_temp(X) :- t(Y), X is Y - 1.
last_get_next_real_temp(X) :- fp(Y), X is Y - 1.

reset_t :- retractall(t(_)), assertz(t(0)).
reset_fp :- retractall(fp(_)), assertz(fp(0)).
reset_l :- retractall(l(_)), assertz(l(0)).

write_arg(int, Val) :- write('t'), write(Val).
write_arg(real, Val) :- write('fp'), write(Val).

write_args([]).
write_args([(Type, Val)]) :- write_arg(Type, Val).
write_args([(Type, Val)|Args]) :- 
                    write_arg(Type, Val), write(','),
                    write_args(Args).

process_expressions([], X, X).
process_expressions([Expr:Type|Exprs], X, Z) :- 
                    ir_expr(Expr:Type), save(X, Type, Y),
                    process_expressions(Exprs, Y, Z).

%ir related
%SECTION:store

ir_store(Id, bool, Kind) :- ir_store(Id, int, Kind).

ir_store(Id, int, local) :- 
                    tab, write('@'), write(Id),
                    write(' <- i_lstore t'), last_get_next_int_temp(X),
                    write(X), nl.

ir_store(Id, int, arg) :- 
                    tab, write('@'), write(Id),
                    write(' <- i_astore t'), last_get_next_int_temp(X),
                    write(X), nl.

ir_store(Id, int, var) :- 
                    tab, write('@'), write(Id),
                    write(' <- i_gstore t'), last_get_next_int_temp(X),
                    write(X), nl.

ir_store(Id, real, local) :- 
                    tab, write('@'), write(Id),
                    write(' <- r_lstore fp'), last_get_next_real_temp(X),
                    write(X), nl.

ir_store(Id, real, arg) :- 
                    tab, write('@'), write(Id),
                    write(' <- r_astore fp'), last_get_next_real_temp(X),
                    write(X), nl.

ir_store(Id, real, var) :-
                    tab, write('@'), write(Id),
                    write(' <- r_gstore fp'), last_get_next_real_temp(X),
                    write(X), nl.

%SECTION:load

ir_load(Id, bool, Kind) :- ir_load(Id, int, Kind).

ir_load(Id, int, local) :- 
                    tab, write('t'), get_next_int_temp(X), 
                    write(X), write(' <- i_lload @'), write(Id),
                    nl.

ir_load(Id, int, arg) :- 
                    tab, write('t'), get_next_int_temp(X),
                    write(X), write(' <- i_aload @'), write(Id),
                    nl.

ir_load(Id, int, var) :- 
                    tab, write('t'), get_next_int_temp(X), 
                    write(X), write(' <- i_gload @'), write(Id),
                    nl.

ir_load(Id, real, local) :-
                    tab, write('fp'), get_next_real_temp(X), 
                    write(X), write(' <- r_lload @'), write(Id),
                    nl.

ir_load(Id, real, arg) :-
                    tab, write('fp'), get_next_real_temp(X), 
                    write(X), write(' <- r_aload @'), write(Id),
                    nl.

ir_load(Id, real, var) :- 
                    tab, write('fp'), get_next_real_temp(X), 
                    write(X), write(' <- r_gload @'), write(Id),
                    nl.

ir_value(Val, int) :- 
                    tab, write('t'), get_next_int_temp(X),
                    write(X), write(' <- i_value '),
                    write(Val), nl.

ir_value(Val, real) :- 
                    tab, write('fp'), get_next_real_temp(X),
                    write(X), write(' <- r_value '),
                    write(Val), nl.

%SECTION:arithm

ir_mul(int, [(_,T1), (_,T2)]) :- 
                    get_next_int_temp(X), tab, write('t'),
                    write(X), write(' <- i_mul t'),
                    write(T1), write(', t'),
                    write(T2), nl.

ir_mul(real, [(_,F1), (_,F2)]) :-
                    get_next_real_temp(X), tab, write('fp'), 
                    write(X), write(' <- r_mul fp'),
                    write(F1), write(', fp'),
                    write(F2), nl.

ir_div(int, [(_,T1), (_,T2)]) :-
                    get_next_int_temp(X), tab, write('t'), 
                    write(X),
                    write(' <- i_div t'), write(T1),
                    write(', t'), write(T2), nl.

ir_div(real, [(_,F1), (_,F2)]) :- 
                    get_next_real_temp(X), tab, write('fp'),
                    write(X),
                    write(' <- r_div fp'), write(F1),
                    write(', fp'), write(F2), nl.

ir_add(int, [(_,T1), (_,T2)]) :- 
                    get_next_int_temp(X), tab, write('t'), write(X),
                    write(' <- i_add t'), write(T1),
                    write(', t'), write(T2), nl.

ir_add(real, [(_,F1), (_,F2)]) :-
                    get_next_real_temp(X), tab, write('fp'), write(X),
                    write(' <- r_add fp'), write(F1),
                    write(', fp'), write(F2), nl.

ir_sub(int, [(_,T1), (_,T2)]) :-
                    get_next_int_temp(X), tab, write('t'), write(X),
                    write(' <- i_sub t'), write(T1),
                    write(', t'), write(T2), nl.

ir_sub(real, [(_,F1), (_,F2)]) :-
                    get_next_real_temp(X), tab, write('fp'), write(X),
                    write(' <- r_sub fp'), write(F1),
                    write(', fp'), write(F2), nl.

ir_mod(int, [(_,T1), (_,T2)]) :- 
                    get_next_int_temp(X), tab, write('t'), write(X),
                    write(' <- mod t'), write(T1),
                    write(', t'), write(T2),
                    nl.

ir_inv(int, [(_,T1)]) :-
                    get_next_int_temp(X), tab, write('t'), write(X),
                    write(' <- i_inv t'), write(T1), 
                    nl.

ir_inv(real, [(_,F1)]) :- 
                    get_next_int_temp(X), tab, write('fp'), write(X),
                    write(' <- r_inv fp'), write(F1), 
                    nl.

%SECTION:logic 

ir_lt(int, [(_,T1), (_,T2)]) :-
                    get_next_int_temp(X), tab, write('t'), write(X),
                    write(' <- i_lt t'), write(T1),
                    write(', t'), write(T2), nl.

ir_lt(real, [(_,F1), (_,F2)]) :- 
                    get_next_int_temp(X), tab, write('t'), write(X),
                    write(' <- r_lt fp'), write(F1),
                    write(', fp'), write(F2), nl.

ir_gt(Type, [(_,V1), (_,V2)]) :- ir_lt(Type, [(_,V2), (_,V1)]).

ir_eq(int, [(_,T1), (_,T2)]) :- 
                    get_next_int_temp(X), tab, write('t'), write(X),
                    write(' <- i_eq t'), write(T1),
                    write(', t'), write(T2), nl.

ir_eq(real, [(_,F1), (_,F2)]) :- 
                    get_next_int_temp(X), tab, write('t'), write(X),
                    write(' <- r_eq fp'), write(F1),
                    write(', fp'), write(F2), nl.

ir_ne(int, [(_,T1), (_,T2)]) :- 
                    get_next_int_temp(X), tab, write('t'), write(X),
                    write(' <- i_ne t'), write(T1),
                    write(', t'), write(T2), nl.

ir_ne(real, [(_,F1), (_,F2)]) :- 
                    get_next_int_temp(X), tab, write('t'), write(X),
                    write(' <- r_ne fp'), write(F1),
                    write(', fp'), write(F2), nl.

ir_le(int, [(_,T1), (_,T2)]) :- 
                    get_next_int_temp(X), tab, write('t'), write(X),
                    write(' <- i_le t'), write(T1),
                    write(', t'), write(T2), nl.

ir_le(real, [(_,F1), (_,F2)]) :- 
                    get_next_int_temp(X), tab, write('t'), write(X),
                    write(' <- i_le fp'), write(F1),
                    write(', fp'), write(F2), nl.

ir_ge(Type, [(_,V1), (_,V2)]) :- ir_le(Type, [(_,V2), (_,V1)]).

ir_not(bool, [(_,T1)]) :- 
                    get_next_int_temp(X), tab, write('t'), write(X),
                    write(' <- i_not t'), write(T1), nl.

%SECTION:coersion

ir_toreal(X) :- 
                    tab, write('fp'), get_next_real_temp(Y),
                    write(Y), write(' <- itor t'),
                    write(X), nl.

%SECTION:copy

ir_copy(int, [T1, T2]) :- 
                    tab, write('t'), write(T1), 
                    write(' <- i_copy t'), write(T2),
                    nl.

ir_copy(real, [F1, F2]) :- 
                    tab, write('fp'), write(F1),
                    write(' <- r_copy fp'), write(F2),
                    nl.

%SECTION:jump

ir_cjump(X, [L1, L2]) :-
                    tab, write('cjump t'), write(X),
                    write(', l'), write(L1), write(' ,l'),
                    write(L2), nl.

ir_jump(L) :- tab, write('jump l'), write(L), nl.

%SECTION:calls

ir_call(int, Id, Args) :- 
                    tab, get_next_int_temp(X), write('t'), 
                    write(X), write(' <- i_call @'), write(Id),
                    write(', ['), write_args(Args), write(']'), nl.

ir_call(real, Id, Args) :- 
                    tab, get_next_real_temp(X), write('fp'),
                    write(X), write(' <- r_call @'), write(Id),
                    write(', ['), write_args(Args), write(']'), nl.

ir_call(nil, Id, Args) :-
                    tab, write('call @'), write(Id),
                    write(', ['), write_args(Args), write(']'), nl.

%SECTION:logic expressions

%REVIEW:not complete
ir_expr(or(Expression1, Expression2) : bool) :- 
                    get_labels(2, [L1, L2]), ir_expr(Expression1),
                    last_get_next_int_temp(X), ir_cjump(X, [L1, L2]), put_label(L2),
                    ir_expr(Expression2), last_get_next_int_temp(Y), ir_copy(int, [X, Y]),
                    put_label(L1), get_next_int_temp(Z), ir_copy(int, [Z, X]).
     
%REVIEW:not complete
ir_expr(and(Expression1, Expression2) : bool) :-
                    get_labels(2, [L1, L2]), ir_expr(Expression1),
                    last_get_next_int_temp(X), ir_cjump(X, [L1, L2]), put_label(L1),
                    ir_expr(Expression2), last_get_next_int_temp(Y), ir_copy(int, [X, Y]), 
                    put_label(L2), get_next_int_temp(Z), ir_copy(int, [Z, X]).

ir_expr(eq(Expression1:Type, Expression2:Type) : bool) :- 
                    ir_expr(Expression1:Type), save([], Type, Z),
                    ir_expr(Expression2:Type), save(Z, Type, W), ir_eq(Type, W).

ir_expr(ne(Expression1:Type, Expression2:Type) : bool) :- 
                    ir_expr(Expression1:Type), save([], Type, Z), 
                    ir_expr(Expression2:Type), save(Z, Type, W), ir_ne(Type, W).

ir_expr(lt(Expression1:Type, Expression2:Type) : bool) :- 
                    ir_expr(Expression1:Type), save([], Type, Z),
                    ir_expr(Expression2:Type), save(Z, Type, W), ir_lt(Type, W).

ir_expr(le(Expression1, Expression2) : bool) :- 
                    ir_expr(Expression1:Type), save([], Type, Z),
                    ir_expr(Expression2:Type), save(Z, Type, W), ir_le(Type, W).

ir_expr(gt(Expression1:Type, Expression2:Type) : bool) :-
                    ir_expr(Expression1:Type), save([], Type, Z),
                    ir_expr(Expression2:Type), save(Z, Type, W), ir_gt(Type, W).

ir_expr(ge(Expression1:Type, Expression2:Type) : bool) :- 
                    ir_expr(Expression1:Type), save([], Type, Z),
                    ir_expr(Expression2:Type), save(Z, Type, W), ir_ge(Type, W).

ir_expr(not(Expression1:Type) : bool) :- 
                    ir_expr(Expression1:Type), save([], Type, Z), ir_not(Type, Z).

%SECTION:arithm expressions

ir_expr(plus(Expression1, Expression2) : Type) :- 
                    ir_expr(Expression1), save([], Type, Z),
                    ir_expr(Expression2), save(Z, Type, W), ir_add(Type, W).

ir_expr(minus(Expression1, Expression2) : Type):- 
                    ir_expr(Expression1), save([], Type, Z),
                    ir_expr(Expression2), save(Z, Type, W), ir_sub(Type, W).

ir_expr(times(Expression1, Expression2):Type) :- 
                    ir_expr(Expression1), save([], Type, Z),
                    ir_expr(Expression2), save(Z, Type, W),  ir_mul(Type, W).

ir_expr(div(Expression1, Expression2) : Type) :- 
                    ir_expr(Expression1), save([], Type, Z),
                    ir_expr(Expression2), save(Z, Type, W), ir_div(Type, W).

ir_expr(mod(Expression1, Expression2) : int) :- 
                    ir_expr(Expression1), save([], Type, Z),
                    ir_expr(Expression2), save(Z, Type, W), ir_mod(int, W).

ir_expr(inv(Expression1) : Type) :- 
                    ir_expr(Expression1), save([], Type, Z),
                    ir_inv(Type, Z).

%atomic 

ir_expr(int_literal(Val): int) :- ir_value(Val, int).
ir_expr(real_literal(Val): real) :- ir_value(Val, real).

ir_expr(true : bool) :- ir_value(1, int).
ir_expr(false : bool) :- ir_value(0, int).

ir_expr(id(Id, Kind, Type): Type) :- ir_load(Id, Type, Kind).

ir_expr(toreal(Expression) : real) :- 
                    ir_expr(Expression), last_get_next_int_temp(X),
                    ir_toreal(X).

ir_expr(call(Id, Expressions):Type) :- 
                    process_expressions(Expressions, [], X),
                    ir_call(Type, Id, X).

%SECTION:io procedures

ir_print(bool, [(_,B1)]) :- 
                    tab, write('b_print t'),
                    write(B1), nl. 

ir_print(int, [(_,T1)]) :- 
                    tab, write('i_print t'),
                    write(T1), nl.

ir_print(real, [(_,F1)]) :-
                    tab, write('r_print fp'),
                    write(F1), nl.

ir_read(bool) :- 
                    tab, get_next_int_temp(X), write('t'),
                    write(X), write(' <- b_read'), nl.

ir_read(int) :- 
                    tab, get_next_int_temp(X), write('t'),
                    write(X), write(' <- i_read'), nl.

ir_read(real) :- 
                    tab, get_next_real_temp(X), write('fp'),
                    write(X), write(' <- r_read'), nl.

%statements 

ir_s_statement(assign(id(Id, Kind, Type), Expression)) :- 
                    ir_expr(Expression), ir_store(Id, Type, Kind).

ir_s_statement(while(Expression, Statement)) :- 
                    get_labels(3, [L1, L2, L3]),  put_label(L1), ir_expr(Expression),
                    last_get_next_int_temp(X), ir_cjump(X, [L2, L3]), 
                    put_label(L2), ir_statement(Statement), ir_jump(L1), put_label(L3).

ir_s_statement(if(Expression, Statement1, nil)) :-
                    get_labels(2, [L1, L2]), ir_expr(Expression),
                    last_get_next_int_temp(X), ir_cjump(X, [L1, L2]),
                    put_label(L1), ir_statement(Statement1), put_label(L2).


ir_s_statement(if(Expression, Statement1, Statement2)) :- 
                    get_labels(3, [L1, L2, L3]), ir_expr(Expression),
                    last_get_next_int_temp(X), ir_cjump(X, [L1, L2]),
                    put_label(L1), ir_statement(Statement1),
                    ir_jump(L3), put_label(L2),
                    ir_statement(Statement2), put_label(L3).

ir_s_statement(print(Expression:Type)) :- 
                    ir_expr(Expression:Type), save([], Type, Z), 
                    ir_print(Type, Z). 

ir_s_statement(read(id(Id, Kind, Type))) :- ir_read(Type), ir_store(Id, Type, Kind).

ir_s_statement(call(Id, Expressions)) :- 
                    process_expressions(Expressions, [], X), ir_call(nil, Id, X).

ir_statement([]).
ir_statement(S) :- ir_s_statement(S).
ir_statement([S|Ss]) :- ir_s_statement(S), ir_statement(Ss).

%function related

write_fun_name(Id) :- write('function @'), write(Id), nl.

ir_process_fun_body(body([], nil, Expression)) :- 
                    ir_process_ret_expression(Expression).

ir_process_fun_body(body(Declarations, Statement, Expression)) :- 
                    ir_process_declarations(Declarations),
                    ir_process_statement(Statement), ir_process_ret_expression(Expression).

ir_process_declarations([]).
ir_process_declarations([D|Ds]) :- ir_declaration(D), ir_process_declarations(Ds).

ir_declaration(local(_, _, nil)).
ir_declaration(local(Id, Type, Expression)) :- ir_expr(Expression), ir_store(Id, Type, local).

ir_process_statement(Statement) :- ir_statement(Statement).

ir_process_ret_expression(nil) :- ir_return(nil).
ir_process_ret_expression(Expression:Type) :- ir_expr(Expression:Type), ir_return(Type).

ir_return(nil) :- tab, write('return'), nl.
ir_return(int) :- tab, write('i_return t'), last_get_next_int_temp(X), write(X), nl.
ir_return(real) :- tab, write('r_return fp'), last_get_next_real_temp(X), write(X), nl.

%ast related

ir_ast_process(var(_, _)).
ir_ast_process(fun(Identifier, _, Body)) :- write_fun_name(Identifier), ir_process_fun_body(Body).

ir_ast_list_process([]).
ir_ast_list_process([AST|ASTs]) :- ir_ast_process(AST), !, ir_ast_list_process(ASTs).

start(Name) :- readfile(Name, AST_List), ir_ast_list_process(AST_List).

start :- 
                    retractall(l(_)), retractall(t(_)), 
                    retractall(fp(_)), assertz(l(0)),
                    assertz(t(0)), assertz(fp(0)), start('ir.in'),
                    retractall(t(_)), retractall(fp(_)), retractall(l(_)),
                    assertz(t(0)), assertz(fp(0)), assertz(l(0)).