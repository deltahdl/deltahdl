#include "parser/parser.h"

namespace delta {

Parser::Parser(Lexer& lexer, Arena& arena, DiagEngine& diag)
    : lexer_(lexer), arena_(arena), diag_(diag) {}

Token Parser::current_token() { return lexer_.peek(); }
bool Parser::check(TokenKind kind) { return current_token().is(kind); }
bool Parser::at_end() { return check(TokenKind::Eof); }
SourceLoc Parser::current_loc() { return current_token().loc; }

Token Parser::consume() { return lexer_.next(); }

bool Parser::match(TokenKind kind) {
    if (!check(kind)) {
        return false;
    }
    consume();
    return true;
}

Token Parser::expect(TokenKind kind) {
    if (check(kind)) {
        return consume();
    }
    auto tok = current_token();
    diag_.error(tok.loc,
        "expected " + std::string(token_kind_name(kind)) +
        ", got " + std::string(token_kind_name(tok.kind)));
    return tok;
}

void Parser::synchronize() {
    while (!at_end()) {
        if (check(TokenKind::Semicolon)) {
            consume();
            return;
        }
        if (check(TokenKind::KwEndmodule) || check(TokenKind::KwEnd)) {
            return;
        }
        consume();
    }
}

// --- Top level ---

CompilationUnit* Parser::parse() {
    auto* unit = arena_.create<CompilationUnit>();
    while (!at_end()) {
        if (check(TokenKind::KwModule)) {
            auto* mod = parse_module_decl();
            if (mod != nullptr) {
                unit->modules.push_back(mod);
            }
        } else {
            diag_.error(current_loc(), "expected module declaration");
            consume();
        }
    }
    return unit;
}

// --- Module parsing ---

ModuleDecl* Parser::parse_module_decl() {
    auto* mod = arena_.create<ModuleDecl>();
    auto loc = current_loc();
    expect(TokenKind::KwModule);

    auto name_tok = expect(TokenKind::Identifier);
    mod->name = name_tok.text;
    mod->range.start = loc;

    if (check(TokenKind::Hash)) {
        // Parameter port list: #(param_decls)
        consume();
        expect(TokenKind::LParen);
        // Simplified: skip parameter parsing for now
        while (!check(TokenKind::RParen) && !at_end()) {
            consume();
        }
        expect(TokenKind::RParen);
    }

    if (check(TokenKind::LParen)) {
        parse_port_list(*mod);
    }

    expect(TokenKind::Semicolon);
    parse_module_body(*mod);
    expect(TokenKind::KwEndmodule);
    mod->range.end = current_loc();
    return mod;
}

void Parser::parse_port_list(ModuleDecl& mod) {
    expect(TokenKind::LParen);
    if (check(TokenKind::RParen)) {
        consume();
        return;
    }
    mod.ports.push_back(parse_port_decl());
    while (match(TokenKind::Comma)) {
        mod.ports.push_back(parse_port_decl());
    }
    expect(TokenKind::RParen);
}

PortDecl Parser::parse_port_decl() {
    PortDecl port;
    port.loc = current_loc();

    if (check(TokenKind::KwInput)) { port.direction = Direction::Input; consume(); }
    else if (check(TokenKind::KwOutput)) { port.direction = Direction::Output; consume(); }
    else if (check(TokenKind::KwInout)) { port.direction = Direction::Inout; consume(); }
    else if (check(TokenKind::KwRef)) { port.direction = Direction::Ref; consume(); }

    port.data_type = parse_data_type();

    auto name_tok = expect(TokenKind::Identifier);
    port.name = name_tok.text;

    if (match(TokenKind::Eq)) {
        port.default_value = parse_expr();
    }
    return port;
}

void Parser::parse_module_body(ModuleDecl& mod) {
    while (!check(TokenKind::KwEndmodule) && !at_end()) {
        auto* item = parse_module_item();
        if (item != nullptr) {
            mod.items.push_back(item);
        }
    }
}

ModuleItem* Parser::parse_module_item() {
    if (check(TokenKind::KwAssign)) {
        return parse_continuous_assign();
    }
    if (check(TokenKind::KwInitial)) {
        return parse_initial_block();
    }
    if (check(TokenKind::KwFinal)) {
        return parse_final_block();
    }
    if (check(TokenKind::KwAlways)) {
        return parse_always_block(AlwaysKind::Always);
    }
    if (check(TokenKind::KwAlwaysComb)) {
        return parse_always_block(AlwaysKind::AlwaysComb);
    }
    if (check(TokenKind::KwAlwaysFF)) {
        return parse_always_block(AlwaysKind::AlwaysFF);
    }
    if (check(TokenKind::KwAlwaysLatch)) {
        return parse_always_block(AlwaysKind::AlwaysLatch);
    }
    if (check(TokenKind::KwParameter) || check(TokenKind::KwLocalparam)) {
        return parse_param_decl();
    }
    // Try net/var declaration
    auto dtype = parse_data_type();
    if (dtype.kind != DataTypeKind::Implicit || check(TokenKind::Identifier)) {
        return parse_net_or_var_decl(dtype);
    }
    diag_.error(current_loc(), "unexpected token in module body");
    synchronize();
    return nullptr;
}

ModuleItem* Parser::parse_continuous_assign() {
    auto* item = arena_.create<ModuleItem>();
    item->kind = ModuleItemKind::ContAssign;
    item->loc = current_loc();
    expect(TokenKind::KwAssign);
    item->assign_lhs = parse_expr();
    expect(TokenKind::Eq);
    item->assign_rhs = parse_expr();
    expect(TokenKind::Semicolon);
    return item;
}

ModuleItem* Parser::parse_param_decl() {
    auto* item = arena_.create<ModuleItem>();
    item->kind = ModuleItemKind::ParamDecl;
    item->loc = current_loc();
    consume(); // parameter or localparam
    item->data_type = parse_data_type();
    auto name_tok = expect(TokenKind::Identifier);
    item->name = name_tok.text;
    if (match(TokenKind::Eq)) {
        item->init_expr = parse_expr();
    }
    expect(TokenKind::Semicolon);
    return item;
}

ModuleItem* Parser::parse_always_block(AlwaysKind kind) {
    auto* item = arena_.create<ModuleItem>();
    item->kind = ModuleItemKind::AlwaysBlock;
    item->always_kind = kind;
    item->loc = current_loc();
    consume(); // always / always_comb / always_ff / always_latch

    if (check(TokenKind::At)) {
        consume();
        if (check(TokenKind::LParen)) {
            consume();
            item->sensitivity = parse_event_list();
            expect(TokenKind::RParen);
        } else if (check(TokenKind::Star)) {
            consume(); // @*
        }
    }

    item->body = parse_stmt();
    return item;
}

ModuleItem* Parser::parse_initial_block() {
    auto* item = arena_.create<ModuleItem>();
    item->kind = ModuleItemKind::InitialBlock;
    item->loc = current_loc();
    consume(); // initial
    item->body = parse_stmt();
    return item;
}

ModuleItem* Parser::parse_final_block() {
    auto* item = arena_.create<ModuleItem>();
    item->kind = ModuleItemKind::FinalBlock;
    item->loc = current_loc();
    consume(); // final
    item->body = parse_stmt();
    return item;
}

ModuleItem* Parser::parse_net_or_var_decl(DataType dtype) {
    auto* item = arena_.create<ModuleItem>();
    item->kind = ModuleItemKind::VarDecl;
    item->loc = current_loc();
    item->data_type = dtype;
    auto name_tok = expect(TokenKind::Identifier);
    item->name = name_tok.text;
    if (match(TokenKind::Eq)) {
        item->init_expr = parse_expr();
    }
    expect(TokenKind::Semicolon);
    return item;
}

ModuleItem* Parser::parse_module_instantiation() {
    auto* item = arena_.create<ModuleItem>();
    item->kind = ModuleItemKind::ModuleInst;
    item->loc = current_loc();
    // Module instantiation is complex; stub for later phases
    synchronize();
    return item;
}

// --- Statements ---

Stmt* Parser::parse_stmt() {
    if (check(TokenKind::KwBegin)) {
        return parse_block_stmt();
    }
    if (check(TokenKind::KwIf)) {
        return parse_if_stmt();
    }
    if (check(TokenKind::KwCase) || check(TokenKind::KwCasex) || check(TokenKind::KwCasez)) {
        auto kind = current_token().kind;
        return parse_case_stmt(kind);
    }
    if (check(TokenKind::KwFor)) {
        return parse_for_stmt();
    }
    if (check(TokenKind::KwWhile)) {
        return parse_while_stmt();
    }
    if (check(TokenKind::KwForever)) {
        return parse_forever_stmt();
    }
    if (check(TokenKind::KwRepeat)) {
        return parse_repeat_stmt();
    }
    if (check(TokenKind::KwFork)) {
        return parse_fork_stmt();
    }
    if (check(TokenKind::Hash)) {
        return parse_delay_stmt();
    }
    if (check(TokenKind::At)) {
        return parse_event_control_stmt();
    }
    return parse_assignment_or_expr_stmt();
}

Stmt* Parser::parse_block_stmt() {
    auto* stmt = arena_.create<Stmt>();
    stmt->kind = StmtKind::Block;
    stmt->range.start = current_loc();
    expect(TokenKind::KwBegin);
    while (!check(TokenKind::KwEnd) && !at_end()) {
        auto* s = parse_stmt();
        if (s != nullptr) {
            stmt->stmts.push_back(s);
        }
    }
    expect(TokenKind::KwEnd);
    stmt->range.end = current_loc();
    return stmt;
}

Stmt* Parser::parse_if_stmt() {
    auto* stmt = arena_.create<Stmt>();
    stmt->kind = StmtKind::If;
    stmt->range.start = current_loc();
    expect(TokenKind::KwIf);
    expect(TokenKind::LParen);
    stmt->condition = parse_expr();
    expect(TokenKind::RParen);
    stmt->then_branch = parse_stmt();
    if (match(TokenKind::KwElse)) {
        stmt->else_branch = parse_stmt();
    }
    return stmt;
}

Stmt* Parser::parse_case_stmt(TokenKind case_kind) {
    auto* stmt = arena_.create<Stmt>();
    stmt->kind = StmtKind::Case;
    stmt->case_kind = case_kind;
    stmt->range.start = current_loc();
    consume(); // case/casex/casez
    expect(TokenKind::LParen);
    stmt->condition = parse_expr();
    expect(TokenKind::RParen);
    while (!check(TokenKind::KwEndcase) && !at_end()) {
        CaseItem item;
        if (match(TokenKind::KwDefault)) {
            item.is_default = true;
        } else {
            item.patterns.push_back(parse_expr());
            while (match(TokenKind::Comma)) {
                item.patterns.push_back(parse_expr());
            }
        }
        expect(TokenKind::Colon);
        item.body = parse_stmt();
        stmt->case_items.push_back(std::move(item));
    }
    expect(TokenKind::KwEndcase);
    return stmt;
}

Stmt* Parser::parse_for_stmt() {
    auto* stmt = arena_.create<Stmt>();
    stmt->kind = StmtKind::For;
    stmt->range.start = current_loc();
    expect(TokenKind::KwFor);
    expect(TokenKind::LParen);
    stmt->for_init = parse_assignment_or_expr_stmt();
    stmt->for_cond = parse_expr();
    expect(TokenKind::Semicolon);
    stmt->for_step = parse_assignment_or_expr_stmt();
    expect(TokenKind::RParen);
    stmt->for_body = parse_stmt();
    return stmt;
}

Stmt* Parser::parse_while_stmt() {
    auto* stmt = arena_.create<Stmt>();
    stmt->kind = StmtKind::While;
    stmt->range.start = current_loc();
    expect(TokenKind::KwWhile);
    expect(TokenKind::LParen);
    stmt->condition = parse_expr();
    expect(TokenKind::RParen);
    stmt->body = parse_stmt();
    return stmt;
}

Stmt* Parser::parse_forever_stmt() {
    auto* stmt = arena_.create<Stmt>();
    stmt->kind = StmtKind::Forever;
    stmt->range.start = current_loc();
    expect(TokenKind::KwForever);
    stmt->body = parse_stmt();
    return stmt;
}

Stmt* Parser::parse_repeat_stmt() {
    auto* stmt = arena_.create<Stmt>();
    stmt->kind = StmtKind::Repeat;
    stmt->range.start = current_loc();
    expect(TokenKind::KwRepeat);
    expect(TokenKind::LParen);
    stmt->condition = parse_expr();
    expect(TokenKind::RParen);
    stmt->body = parse_stmt();
    return stmt;
}

Stmt* Parser::parse_fork_stmt() {
    auto* stmt = arena_.create<Stmt>();
    stmt->kind = StmtKind::Fork;
    stmt->range.start = current_loc();
    expect(TokenKind::KwFork);
    while (!check(TokenKind::KwJoin) && !check(TokenKind::KwJoinAny) &&
           !check(TokenKind::KwJoinNone) && !at_end()) {
        auto* s = parse_stmt();
        if (s != nullptr) {
            stmt->fork_stmts.push_back(s);
        }
    }
    stmt->join_kind = current_token().kind;
    consume(); // join / join_any / join_none
    return stmt;
}

Stmt* Parser::parse_assignment_or_expr_stmt() {
    auto* stmt = arena_.create<Stmt>();
    stmt->range.start = current_loc();
    auto* lhs_expr = parse_expr();

    if (match(TokenKind::Eq)) {
        stmt->kind = StmtKind::BlockingAssign;
        stmt->lhs = lhs_expr;
        stmt->rhs = parse_expr();
    } else if (match(TokenKind::LtEq)) {
        stmt->kind = StmtKind::NonblockingAssign;
        stmt->lhs = lhs_expr;
        stmt->rhs = parse_expr();
    } else {
        stmt->kind = StmtKind::ExprStmt;
        stmt->expr = lhs_expr;
    }
    expect(TokenKind::Semicolon);
    return stmt;
}

// --- Types ---

DataType Parser::parse_data_type() {
    DataType dtype;
    switch (current_token().kind) {
    case TokenKind::KwLogic: dtype.kind = DataTypeKind::Logic; consume(); break;
    case TokenKind::KwReg: dtype.kind = DataTypeKind::Reg; consume(); break;
    case TokenKind::KwBit: dtype.kind = DataTypeKind::Bit; consume(); break;
    case TokenKind::KwByte: dtype.kind = DataTypeKind::Byte; consume(); break;
    case TokenKind::KwShortint: dtype.kind = DataTypeKind::Shortint; consume(); break;
    case TokenKind::KwInt: dtype.kind = DataTypeKind::Int; consume(); break;
    case TokenKind::KwLongint: dtype.kind = DataTypeKind::Longint; consume(); break;
    case TokenKind::KwInteger: dtype.kind = DataTypeKind::Integer; consume(); break;
    case TokenKind::KwReal: dtype.kind = DataTypeKind::Real; consume(); break;
    case TokenKind::KwTime: dtype.kind = DataTypeKind::Time; consume(); break;
    case TokenKind::KwString: dtype.kind = DataTypeKind::String; consume(); break;
    case TokenKind::KwWire: dtype.kind = DataTypeKind::Logic; consume(); break;
    default: return dtype; // Implicit
    }

    if (match(TokenKind::KwSigned)) {
        dtype.is_signed = true;
    } else if (match(TokenKind::KwUnsigned)) {
        dtype.is_signed = false;
    }

    if (check(TokenKind::LBracket)) {
        consume();
        dtype.packed_dim_left = parse_expr();
        expect(TokenKind::Colon);
        dtype.packed_dim_right = parse_expr();
        expect(TokenKind::RBracket);
    }
    return dtype;
}

// --- Event lists ---

std::vector<EventExpr> Parser::parse_event_list() {
    std::vector<EventExpr> events;
    events.push_back(parse_single_event());
    while (match(TokenKind::KwOr) || match(TokenKind::Comma)) {
        events.push_back(parse_single_event());
    }
    return events;
}

EventExpr Parser::parse_single_event() {
    EventExpr ev;
    if (match(TokenKind::KwPosedge)) {
        ev.edge = Edge::Posedge;
    } else if (match(TokenKind::KwNegedge)) {
        ev.edge = Edge::Negedge;
    }
    ev.signal = parse_expr();
    return ev;
}

Stmt* Parser::parse_delay_stmt() {
    auto* stmt = arena_.create<Stmt>();
    stmt->kind = StmtKind::Delay;
    stmt->range.start = current_loc();
    expect(TokenKind::Hash);
    stmt->delay = parse_primary_expr();
    stmt->body = parse_stmt();
    return stmt;
}

Stmt* Parser::parse_event_control_stmt() {
    auto* stmt = arena_.create<Stmt>();
    stmt->kind = StmtKind::EventControl;
    stmt->range.start = current_loc();
    expect(TokenKind::At);
    if (match(TokenKind::Star)) {
        // @* — implicit sensitivity
    } else {
        expect(TokenKind::LParen);
        stmt->events = parse_event_list();
        expect(TokenKind::RParen);
    }
    stmt->body = parse_stmt();
    return stmt;
}

} // namespace delta
