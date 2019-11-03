:- dynamic t/1.
:- dynamic fp/1.
:- dynamic l/1.

t(0).
fp(0).
l(0).

%function related

write_fun_name(Id) :- write('function @'), write(Id), nl.

ir_process_fun_body(body([], nil, Expression)) :- ir_process_ret_expression(Expression).
ir_process_fun_body(body(Declarations, Statement, Expression)) :- ir_process_declarations(Declarations),
                                                                ir_process_statement(Statement), ir_process_ret_expression(Expression).

ir_process_declarations([]).
ir_process_declarations([D|Ds]) :- ir_declaration(D), ir_process_declarations(Ds).

ir_declaration(local(_, _, nil)).
ir_declaration(local(Id, Type, Expression)) :- ir_process_expression(Expression), write


%ast related

ir_ast_process(var(ID, _)) :- write(ID).
ir_ast_process(fun(Identifier, _, Body)) :- write_fun_name(Identifier), ir_process_fun_body(Body).

ir_ast_list_process([]).
ir_ast_list_process([AST|ASTs]) :- ir_ast_process(AST), ir_ast_list_process(ASTs).

readfile(Name, X) :- open(Name, read, In), read_term(In, X, []), close(In).

start(Name) :- readfile(Name, AST_List), ir_ast_list_process(AST_List).