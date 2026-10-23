#include <algorithm>
#include <cstddef>
#include <string_view>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "lexer/token.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"
#include "parser/parser.h"
#include "parser/parser_data_decl_internal.h"

namespace delta {

namespace {

// §13.3: a leading direction keyword (or the const-as-ref qualifier) opens a
// tf_port_declaration.
bool IsTfPortDirectionKw(TokenKind tk) {
  return tk == TokenKind::kKwInput || tk == TokenKind::kKwOutput ||
         tk == TokenKind::kKwInout || tk == TokenKind::kKwRef ||
         tk == TokenKind::kKwConst;
}

// §13.3 (printed page 337): a formal whose data type is not declared is
// `logic` where its direction is written, and a tf_port_declaration always
// writes one, so an implicit type is `logic` with whatever signing and packed
// dimensions it carries: `input signed [7:0] a;` is a `logic signed [7:0]`.
// The simulator converts an actual to its formal's declared type and to none
// where the formal's type is implicit, so an implicit `[7:0]` left as it was
// kept all nine bits of 16'h01FF. Pure state update.
void DefaultImplicitToLogic(DataType& dt) {
  if (dt.kind == DataTypeKind::kImplicit) dt.kind = DataTypeKind::kLogic;
}

}  // namespace

// The header of one tf_port_declaration, its direction, its const and static
// qualifiers and its data type, which every declarator ParseTfPortDeclarators
// reads after it shares.
struct TfPortHeader {
  Direction dir = Direction::kInput;
  bool is_const = false;
  bool is_ref_static = false;
  DataType dt;
};

// Consume the leading direction keyword of a tf_port_declaration. The 'const'
// qualifier (already consumed by the caller) is mapped to 'ref'.
Direction Parser::ParseTfPortDirection() {
  if (Check(TokenKind::kKwInput)) {
    Consume();
    return Direction::kInput;
  }
  if (Check(TokenKind::kKwOutput)) {
    Consume();
    return Direction::kOutput;
  }
  if (Check(TokenKind::kKwInout)) {
    Consume();
    return Direction::kInout;
  }
  Consume();
  return Direction::kRef;
}

// Parse the comma-separated declarators that share one tf_port_declaration
// header (direction/const/static and data type), appending each to item.
void Parser::ParseTfPortDeclarators(ModuleItem* item, const TfPortHeader& hdr) {
  do {
    FunctionArg arg;
    arg.is_const = hdr.is_const;
    arg.is_ref_static = hdr.is_ref_static;
    arg.direction = hdr.dir;
    arg.data_type = hdr.dt;
    arg.name = Expect(TokenKind::kIdentifier, Subclause("13.3")).text;
    ParseUnpackedDims(arg.unpacked_dims);
    if (Match(TokenKind::kEq)) {
      arg.default_value = ParseExpr();
    }
    item->func_args.push_back(arg);
  } while (Match(TokenKind::kComma));
  Expect(TokenKind::kSemicolon, Subclause("13.3"));
}

// A.2.7: `tf_port_direction ::= port_direction | [ const ] ref [ static ]`, so
// `const` opens a tf_port_declaration only where it qualifies a `ref`. Standing
// alone it opens a data_declaration instead: `const int c = a + 1;` at the head
// of a subroutine body is a block_item_declaration (A.2.8).
bool Parser::IsTfPortDeclarationStart() {
  auto tk = CurrentToken().kind;
  if (tk != TokenKind::kKwConst) return IsTfPortDirectionKw(tk);
  auto saved = lexer_.SavePos();
  Consume();
  bool qualifies_ref = Check(TokenKind::kKwRef);
  lexer_.RestorePos(saved);
  return qualifies_ref;
}

// A.2.7's tf_port_declaration, read into `item`'s formals where one opens
// here, past the attribute instances it may begin with; false, with nothing
// read, where none opens. The names it declares with an implicit data type are
// added to `untyped`, a body declaration of one of them being its type
// (§13.3). The look past the attributes reports nothing, since a statement or
// a declaration they open reads them again.
bool Parser::TryParseTfPortDeclaration(
    ModuleItem* item, std::unordered_set<std::string_view>& untyped) {
  auto saved = lexer_.SavePos();
  diag_.PushSuppress();
  ParseAttributes();
  bool opens = IsTfPortDeclarationStart();
  diag_.PopSuppress();
  lexer_.RestorePos(saved);
  if (!opens) return false;
  ParseAttributes();
  TfPortHeader hdr;
  hdr.is_const = Match(TokenKind::kKwConst);
  hdr.dir = ParseTfPortDirection();
  hdr.is_ref_static =
      (hdr.dir == Direction::kRef) && Match(TokenKind::kKwStatic);
  bool has_var = Match(TokenKind::kKwVar);
  // A.2.2.1 lets the data type be a type_identifier behind a package or class
  // scope, `input pk::t x;`, which ParseDeclaredDataType reads past
  // known_types_, or a type_reference, which a formal writes after `var`
  // (§6.23).
  bool implicit_type = false;
  if (!ParserDataDeclHelpers::ReadKeyedTypeReference(*this, hdr.dt, has_var,
                                                     false)) {
    hdr.dt = ParseDeclaredDataType();
    // A.2.7's tf_port_declaration takes a data_type_or_implicit, and A.2.2.1's
    // implicit_data_type may be packed dimensions alone: `input [7:0] a;`
    // names no type and no signing, and ParseDataType leaves the range unread
    // when nothing precedes it.
    implicit_type = hdr.dt.kind == DataTypeKind::kImplicit;
    if (implicit_type) ParsePackedDims(hdr.dt);
    DefaultImplicitToLogic(hdr.dt);
  }

  size_t first = item->func_args.size();
  ParseTfPortDeclarators(item, hdr);
  if (implicit_type) {
    for (size_t i = first; i < item->func_args.size(); ++i) {
      untyped.insert(item->func_args[i].name);
    }
  }
  return true;
}

// §13.3 (printed page 336): a formal a body declares by its direction alone,
// its data type implicit, takes its type from a data declaration of its name
// later in the body, as the clause's mytask2 writes `output x;` and then
// `int x;`. Each of `item`'s body declarations from `first` on that names one
// of `untyped` becomes that formal's type and leaves the body. A parameter,
// or a variable declared with an initial value, stays a declaration of its
// own, and so does a second declaration of a formal already typed.
static void TypeFormalsFromBodyDecls(
    ModuleItem* item, size_t first,
    std::unordered_set<std::string_view>& untyped) {
  auto& stmts = item->func_body_stmts;
  for (size_t i = first; i < stmts.size();) {
    const Stmt* decl = stmts[i];
    if (decl->kind != StmtKind::kVarDecl || decl->var_is_param ||
        decl->var_init != nullptr || untyped.erase(decl->var_name) == 0) {
      ++i;
      continue;
    }
    auto formal =
        std::ranges::find(item->func_args, decl->var_name, &FunctionArg::name);
    formal->data_type = decl->var_decl_type;
    formal->unpacked_dims = decl->var_unpacked_dims;
    stmts.erase(stmts.begin() + static_cast<std::ptrdiff_t>(i));
  }
}

// A.2.6 and A.2.7: a subroutine body up to `end_kw`. Without a port list in
// parentheses it opens with tf_item_declarations, each a tf_port_declaration
// or a block_item_declaration in either order (§13.3, §13.4), and after a
// port list with block_item_declarations alone; its statements follow. A port
// declaration is read wherever it stands and reported, under `subclause`,
// where the grammar admits none: after a port list, or after the body's first
// statement.
void Parser::ParseSubroutineBody(ModuleItem* item, TokenKind end_kw,
                                 Subclause subclause) {
  std::unordered_set<std::string_view> untyped;
  bool before_stmts = true;
  while (!Check(end_kw) && !AtEnd()) {
    SourceLoc loc = CurrentLoc();
    if (TryParseTfPortDeclaration(item, untyped)) {
      if (item->is_ansi_ports) {
        diag_.Error(loc,
                    "a task or function whose ports are listed in parentheses "
                    "cannot declare a port in its body",
                    subclause);
      } else if (!before_stmts) {
        diag_.Error(loc,
                    "a port declaration cannot follow a statement in a task "
                    "or function body",
                    subclause);
      }
      continue;
    }
    if (IsBlockVarDeclStart()) {
      size_t first = item->func_body_stmts.size();
      ParseBlockVarDecls(item->func_body_stmts);
      TypeFormalsFromBodyDecls(item, first, untyped);
    } else if (!RejectMisplacedStmtLabel()) {
      before_stmts = false;
      item->func_body_stmts.push_back(ParseStmt());
    }
  }
}

}  // namespace delta
