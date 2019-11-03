:- dynamic t/1.
:- dynamic fp/1.
:- dynamic l/1.

t(0).
fp(0).
l(0).

tab :- tab(4).

save(X, int, Z) :- t(W), Y is W - 1, append(X, [(int, Y)], Z).
save(X, real, Z) :- fp(W), Y is W - 1, append(X, [(real, Y)], Z).

put_label(X) :- write('l'), write(X), write(':'). 

get_labels(0, []).
get_labels(N, [L|Ls]) :- l(L), increment_l, N1 is N - 1, get_labels(N1, Ls).  

increment_t :- t(X), Y is X + 1, asserta(t(Y)). 
increment_fp :- fp(X), Y is X + 1, asserta(fp(Y)). 
increment_l :- l(X), Y is X + 1, asserta(l(Y)). 

last_t(X) :- t(Y), X is Y - 1.
last_fp(X) :- fp(Y), X is Y - 1.

reset_t :- retractall(t(_)), assertz(t(0)).
reset_fp :- retractall(fp(_)), assertz(fp(0)).

%ir related
%SECTION:store

ir_store(Id, int, local) :- tab, write('@'), write(Id), write(' <- i_lstore t'), last_t(X), write(X), nl.
ir_store(Id, int, arg) :- tab, write('@'), write(Id), write(' <- i_astore t'), last_t(X), write(X), nl.
ir_store(Id, int, var) :- tab, write('@'), write(Id), write(' <- i_gstore t'), last_t(X), write(X), nl.

ir_store(Id, real, local) :- tab, write('@'), write(Id), write(' <- r_lstore fp'), last_fp(X), !, write(X), nl.
ir_store(Id, real, arg) :- tab, write('@'), write(Id), write(' <- r_astore fp'), last_fp(X), !, write(X), nl.
ir_store(Id, real, var) :- tab, write('@'), write(Id), write(' <- r_gstore fp'), last_fp(X), !, write(X), nl.

%SECTION:load

ir_load(Id, int, local) :- tab, write('t'), t(X), write(X), write(' <- i_lload @'), write(Id), nl, increment_t.
ir_load(Id, int, arg) :- tab, write('t'), t(X), write(X), write(' <- i_aload @'), write(Id), nl, increment_t.
ir_load(Id, int, var) :- tab, write('t'), t(X), write(X), write(' <- i_gload @'), write(Id), nl, increment_t.

ir_load(Id, real, local) :- tab, write('fp'), fp(X), write(X), write(' <- r_lload @'), write(Id), nl, increment_fp.
ir_load(Id, real, arg) :- tab, write('fp'), fp(X), write(X), write(' <- r_aload @'), write(Id), nl, increment_fp.
ir_load(Id, real, var) :- tab, write('fp'), fp(X), write(X), write(' <- r_gload @'), write(Id), nl, increment_fp.

ir_value(Val, int) :- tab, write('t'), t(X), write(X), write(' <- i_value '), write(Val), nl, increment_t.
ir_value(Val, real) :- tab, write('fp'), fp(X), write(X), write(' <- r_value '), write(Val), nl, increment_fp.

%SECTION:arithm

ir_mul(int, [(_,T1), (_,T2)]) :- t(X), tab, write('t'), write(X), write(' <- i_mul t'), write(T1), write(', t'), write(T2), nl, increment_t.
ir_mul(real, [(_,F1), (_,F2)]) :- fp(X), tab, write('fp'), write(X), write(' <- r_mul fp'), write(F1), write(', fp'), write(F2), nl, increment_fp.

ir_add(int, [(_,T1), (_,T2)]) :- t(X), tab, write('t'), write(X), write(' <- i_add t'), write(T1), write(', t'), write(T2), nl, increment_t.
ir_add(real, [(_,F1), (_,F2)]) :- fp(X), tab, write('fp'), write(X), write(' <- r_add fp'), write(F1), write(', fp'), write(F2), nl, increment_fp.

ir_sub(int, [(_,T1), (_,T2)]) :- t(X), tab, write('t'), write(X), write(' <- i_sub t'), write(T1), write(', t'), write(T2), nl, increment_t.
ir_sub(real, [(_,F1), (_,F2)]) :- fp(X), tab, write('fp'), write(X), write(' <- r_sub fp'), write(F1), write(', fp'), write(F2), nl, increment_fp.

%SECTION:logic

ir_lt(int, [(_,T1), (_,T2)]) :- t(X), tab, write('t'), write(X), write(' <- i_lt t'), write(T1), write(', t'), write(T2), nl, increment_t.
ir_lt(real, [(_,F1), (_,F2)]) :- fp(X), tab, write('fp'), write(X), write(' <- r_lt fp'), write(F1), write(', fp'), write(F2), nl, increment_fp.

ir_gt(int, [(_,T1), (_,T2)]) :- ir_lt(int, [(_,T2), (_,T1)]).
ir_gt(real, [(_,F1), (_,F2)]) :- ir_lt(real, [(_,F2), (_,F1)]).

ir_eq(int, [(_,T1), (_,T2)]) :- t(X), tab, write('t'), write(X), write(' <- i_eq t'), write(T1), write(', t'), write(T2), nl, increment_t.
ir_eq(real, [(_,F1), (_,F2)]) :- fp(X), tab, write('fp'), write(X), write(' <- r_eq fp'), write(F1), write(', fp'), write(F2), nl, increment_fp.

ir_toreal(X) :- tab, write('fp'), fp(Y), write(Y), write(' <- itor t'), write(X), nl, increment_fp.

%SECTION:jump

ir_cjump(lt(_,_):_, X, [L1, L2]) :- tab, write('cjump t'), write(X), write(', l'), write(L1), write(' ,l'), write(L2), nl.
ir_cjump(gt(_,_):_, X, [L1, L2]) :- tab, write('cjump t'), write(X), write(', l'), write(L1), write(' ,l'), write(L2), nl.

ir_cjump(ge(_,_):_, X, [L1, L2]) :- tab, write('cjump t'), write(X), write(', l'), write(L2), write(' ,l'), write(L1), nl.
ir_cjump(le(_,_):_, X, [L1, L2]) :- tab, write('cjump t'), write(X), write(', l'), write(L2), write(' ,l'), write(L1), nl.

ir_cjump(eq(_,_):_, X, [L1, L2]) :- tab, write('cjump t'), write(X), write(', l'), write(L1), write(' ,l'), write(L2), nl.

ir_jump(L) :- tab, write('jump l'), write(L), nl.

write_arg(int, Val) :- write('t'), write(Val).
write_arg(real, Val) :- write('fp'), write(Val).

write_args([]).
write_args([(Type, Val)]) :- write_arg(Type, Val).
write_args([(Type, Val)|Args]) :- write_arg(Type, Val), write(','), write_args(Args).

ir_call(int, Id, Args) :- tab, t(X), write('t'), write(X), write(' <- i_call @'), write(Id),
                            write(', ['), write_args(Args), write(']'), nl, increment_t.

ir_call(real, Id, Args) :- tab, fp(X), write('fp'), write(X), write(' <- r_call @'), write(Id),
                            write(', ['), write_args(Args), write(']'), nl, increment_fp.
%SECTION:logic expressions

ir_expr(or(Expression1, Expression2) : bool).
ir_expr(and(Expression1, Expression2) : bool).

ir_expr(eq(Expression1:Type, Expression2:Type) : bool) :- ir_expr(Expression1:Type), save([], Type, Z),
    ir_expr(Expression2:Type), save(Z, Type, W), ir_eq(Type, W).

ir_expr(ne(Expression1, Expression2) : bool).

ir_expr(lt(Expression1:Type, Expression2:Type) : bool) :- ir_expr(Expression1:Type), save([], Type, Z),
    ir_expr(Expression2:Type), save(Z, Type, W), ir_lt(Type, W).

ir_expr(le(Expression1, Expression2) : bool) :- ir_expr(Expression1:Type), save([], Type, Z),
    ir_expr(Expression2:Type), save(Z, Type, W), ir_gt(Type, W).

ir_expr(gt(Expression1:Type, Expression2:Type) : bool) :- ir_expr(Expression1:Type), save([], Type, Z),
    ir_expr(Expression2:Type), save(Z, Type, W), ir_gt(Type, W).

ir_expr(ge(Expression1:Type, Expression2:Type) : bool) :- ir_expr(Expression1:Type), save([], Type, Z),
    ir_expr(Expression2:Type), save(Z, Type, W), ir_lt(Type, W).

ir_expr(not(Expression1) : bool).

%SECTION:arithm expressions

ir_expr(plus(Expression1, Expression2) : Type) :- ir_expr(Expression1), save([], Type, Z),
    ir_expr(Expression2), save(Z, Type, W), ir_add(Type, W).

ir_expr(minus(Expression1, Expression2) : Type):- ir_expr(Expression1), save([], Type, Z),
    ir_expr(Expression2), save(Z, Type, W), ir_sub(Type, W).

ir_expr(times(Expression1, Expression2):Type) :- ir_expr(Expression1), save([], Type, Z),
    ir_expr(Expression2), save(Z, Type, W),  ir_mul(Type, W).

ir_expr(div(Expression1, Expression2) : Type).
ir_expr(mod(Expression1, Expression2) : int).
ir_expr(inv(Expression1) : Type).

%atomic 

ir_expr(int_literal(Val): int) :- ir_value(Val, int).
ir_expr(real_literal(Val): real) :- ir_value(Val, real).

ir_expr(true : bool) :- ir_value(1, int).
ir_expr(false : bool) :- ir_value(0, int).

ir_expr(id(Id, Kind, Type): Type) :- ir_load(Id, Type, Kind).

ir_expr(toreal(Expression) : real) :- ir_expr(Expression), last_t(X), ir_toreal(X).

ir_expr(call(Id, Expressions):Type) :- process_expressions(Expressions, [], X), ir_call(Type, Id, X).

process_expressions([], X, X).
process_expressions([Expr|Exprs], X, Z) :- ir_expr(Expr), save(X, int, Y), process_expressions(Exprs, Y, Z).


%statements 

ir_s_statement(assign(id(Id, Kind, Type), Expression)) :- ir_expr(Expression), ir_store(Id, Type, Kind).

ir_s_statement(while(Expression, Statement)) :- get_labels(3, [L1, L2, L3]),  put_label(L1), ir_expr(Expression), last_t(X), ir_cjump(Expression, X, [L2, L3]), put_label(L2),
                                                ir_statement(Statement), ir_jump(L1), put_label(L3).

%ir_s_statement(if(Expression, Statement1, Statement2)).
ir_s_statement(if(Expression, Statement1, nil)) :- get_labels(2, [L1, L2]), ir_expr(Expression),
                                                    last_t(X), ir_cjump(Expression, X, [L1, L2]), put_label(L1),
                                                    ir_statement(Statement1), put_label(L2).

ir_s_statement(print(Expression)) :- ir_expr(Expression). %TODO: load and print
ir_s_statement(read(id(Id, Kind, Type))). %TODO: read and store

ir_s_statement(call(Id, Expressions):Type) :- write('call').

ir_statement([]).
ir_statement(S) :- ir_s_statement(S).
ir_statement([S|Ss]) :- ir_s_statement(S), !, ir_statement(Ss).

%function related

write_fun_name(Id) :- write('function @'), write(Id), nl.

ir_process_fun_body(body([], nil, Expression)) :- ir_process_ret_expression(Expression).
ir_process_fun_body(body(Declarations, Statement, Expression)) :- ir_process_declarations(Declarations),
                                                                ir_process_statement(Statement), ir_process_ret_expression(Expression).

ir_process_declarations([]).
ir_process_declarations([D|Ds]) :- ir_declaration(D), ir_process_declarations(Ds).

ir_declaration(local(_, _, nil)).
ir_declaration(local(Id, Type, Expression)) :- ir_expr(Expression), ir_store(Id, Type, local).

ir_process_statement(Statement) :- ir_statement(Statement).

ir_process_ret_expression(nil) :- ir_return(nil).
ir_process_ret_expression(Expression:Type) :- ir_expr(Expression:Type), ir_return(Type).

ir_return(nil) :- tab, write('return'), nl.
ir_return(int) :- tab, write('i_return t'), last_t(X), write(X), nl.
ir_return(real) :- tab, write('r_return fp'), last_fp(X), write(X), nl.

%ast related

ir_ast_process(var(_, _)).
ir_ast_process(fun(Identifier, _, Body)) :- write_fun_name(Identifier), ir_process_fun_body(Body).

ir_ast_list_process([]).
ir_ast_list_process([AST|ASTs]) :- ir_ast_process(AST), !, ir_ast_list_process(ASTs).

readfile(Name, X) :- open(Name, read, In), read_term(In, X, []), close(In).

start(Name) :- readfile(Name, AST_List), ir_ast_list_process(AST_List).

start :- retractall(l(_)), retractall(t(_)), retractall(fp(_)), assertz(l(0)),
        assertz(t(0)), assertz(fp(0)), start('ir.in'), retractall(t(_)), retractall(fp(_)), retractall(l(_)),
        assertz(t(0)), assertz(fp(0)), assertz(l(0)).