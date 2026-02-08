#pragma once

#include "common/arena.h"
#include "common/diagnostic.h"
#include "lexer/lexer.h"
#include "parser/ast.h"

namespace delta {

class Parser {
   public:
    Parser(Lexer& lexer, Arena& arena, DiagEngine& diag);

    CompilationUnit* parse();

   private:
    // Module parsing
    ModuleDecl* parse_module_decl();
    void parse_port_list(ModuleDecl& mod);
    PortDecl parse_port_decl();
    void parse_module_body(ModuleDecl& mod);
    ModuleItem* parse_module_item();

    // Declarations
    ModuleItem* parse_net_or_var_decl(DataType dtype);
    ModuleItem* parse_continuous_assign();
    ModuleItem* parse_param_decl();
    ModuleItem* parse_always_block(AlwaysKind kind);
    ModuleItem* parse_initial_block();
    ModuleItem* parse_final_block();
    ModuleItem* parse_module_instantiation();

    // Statements
    Stmt* parse_stmt();
    Stmt* parse_block_stmt();
    Stmt* parse_if_stmt();
    Stmt* parse_case_stmt(TokenKind case_kind);
    Stmt* parse_for_stmt();
    Stmt* parse_while_stmt();
    Stmt* parse_forever_stmt();
    Stmt* parse_repeat_stmt();
    Stmt* parse_fork_stmt();
    Stmt* parse_assignment_or_expr_stmt();
    Stmt* parse_delay_stmt();
    Stmt* parse_event_control_stmt();

    // Expressions (Pratt parser — in expr_parser.cpp)
    Expr* parse_expr();
    Expr* parse_expr_bp(int min_bp);
    Expr* parse_prefix_expr();
    Expr* parse_primary_expr();
    Expr* parse_call_expr(Expr* callee);
    Expr* parse_select_expr(Expr* base);
    Expr* parse_system_call();
    Expr* parse_concatenation();

    // Types
    DataType parse_data_type();

    // Event lists
    std::vector<EventExpr> parse_event_list();
    EventExpr parse_single_event();

    // Utilities
    Token expect(TokenKind kind);
    bool match(TokenKind kind);
    Token consume();
    Token current_token();
    bool check(TokenKind kind);
    bool at_end();
    SourceLoc current_loc();
    void synchronize();

    Lexer& lexer_;
    Arena& arena_;
    DiagEngine& diag_;
};

} // namespace delta
