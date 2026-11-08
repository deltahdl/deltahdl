#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"
#include "parser/parser.h"
#include "parser/parser_data_decl_internal.h"
#include "parser/parser_type_name_scope.h"

namespace delta {

namespace {

void InheritRefQualifiers(const std::vector<FunctionArg>& args,
                          FunctionArg& arg, bool dir_explicit) {
  if (dir_explicit || arg.direction != Direction::kRef || args.empty()) return;
  const auto& prev = args.back();
  if (prev.direction != Direction::kRef) return;
  arg.is_const = arg.is_const || prev.is_const;
  arg.is_ref_static = arg.is_ref_static || prev.is_ref_static;
}

void ResolveImplicitArgDataType(FunctionArg& arg,
                                const DataType& prev_data_type,
                                bool dir_explicit, bool first_arg,
                                bool prev_was_default) {
  if (arg.data_type.kind != DataTypeKind::kImplicit ||
      arg.data_type.type_ref_expr != nullptr) {
    return;
  }
  if (arg.data_type.packed_dim_left != nullptr || arg.data_type.is_signed) {
    arg.data_type.kind = DataTypeKind::kLogic;
    return;
  }
  if (first_arg || dir_explicit || prev_was_default) {
    arg.data_type.kind = DataTypeKind::kLogic;
  } else {
    arg.data_type = prev_data_type;
  }
}

DataTypeKind ForwardAggregateKind(TokenKind kw) {
  switch (kw) {
    case TokenKind::kKwEnum:
      return DataTypeKind::kEnum;
    case TokenKind::kKwStruct:
      return DataTypeKind::kStruct;
    case TokenKind::kKwUnion:
      return DataTypeKind::kUnion;
    default:
      return DataTypeKind::kImplicit;
  }
}

bool IsAggregateKw(TokenKind tk) {
  return tk == TokenKind::kKwEnum || tk == TokenKind::kKwStruct ||
         tk == TokenKind::kKwUnion;
}

bool IsDirectionQualifierKw(TokenKind tk) {
  return tk == TokenKind::kKwRef || tk == TokenKind::kKwInput ||
         tk == TokenKind::kKwOutput || tk == TokenKind::kKwInout;
}

}  // namespace

static bool IsHierarchicalParameterName(const Expr* target) {
  while (target->kind == ExprKind::kMemberAccess &&
         !target->is_scope_resolution) {
    target = target->lhs;
    while (target->kind == ExprKind::kSelect) target = target->base;
  }
  return target->kind == ExprKind::kIdentifier &&
         (target->scope_prefix.empty() || target->scope_prefix == "$root");
}

ModuleItem* Parser::ParseDefparam() {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kDefparam;
  item->loc = CurrentLoc();
  Expect(TokenKind::kKwDefparam, Subclause("23.10.1"));

  do {
    SourceLoc target_loc = CurrentLoc();
    Expr* path = ParseExpr();
    if (!IsHierarchicalParameterName(path)) {
      diag_.Error(target_loc,
                  "a defparam's target is a hierarchical parameter name, not "
                  "an expression",
                  Subclause("A.2.4"));
    }
    Expect(TokenKind::kEq, Subclause("23.10.1"));
    Expr* value = ParseMinTypMaxExpr();
    item->defparam_assigns.emplace_back(path, value);
  } while (Match(TokenKind::kComma));
  Expect(TokenKind::kSemicolon, Subclause("23.10.1"));
  return item;
}

bool Parser::TryForwardClassTypedef(ModuleItem* item) {
  if (!Check(TokenKind::kKwClass) && !Check(TokenKind::kKwInterface)) {
    return false;
  }
  Consume();
  if (Check(TokenKind::kKwClass)) Consume();
  item->name = Expect(TokenKind::kIdentifier, Subclause("6.18")).text;
  item->forward_type_kind = DataTypeKind::kNamed;
  known_types_.insert(item->name);
  Expect(TokenKind::kSemicolon, Subclause("6.18"));
  return true;
}

bool Parser::TryForwardAggregateTypedef(ModuleItem* item) {
  if (!IsAggregateKw(CurrentToken().kind)) {
    return false;
  }
  auto saved = lexer_.SavePos();
  DataTypeKind fwd_kind = ForwardAggregateKind(CurrentToken().kind);
  Consume();
  if (CheckIdentifier()) {
    auto id_saved = lexer_.SavePos();
    auto id_tok = Consume();
    if (Check(TokenKind::kSemicolon)) {
      item->name = id_tok.text;
      item->forward_type_kind = fwd_kind;
      known_types_.insert(item->name);
      Expect(TokenKind::kSemicolon, Subclause("6.18"));
      return true;
    }
    lexer_.RestorePos(id_saved);
  }
  lexer_.RestorePos(saved);
  return false;
}

bool Parser::TryForwardBareTypedef(ModuleItem* item) {
  if (!CheckIdentifier()) return false;
  auto saved = lexer_.SavePos();
  auto id_tok = Consume();
  if (Check(TokenKind::kSemicolon)) {
    item->name = id_tok.text;
    known_types_.insert(item->name);
    Expect(TokenKind::kSemicolon, Subclause("6.18"));
    return true;
  }
  lexer_.RestorePos(saved);
  return false;
}

void Parser::SkipBalancedParens() {
  if (!Check(TokenKind::kLParen)) return;
  Consume();
  int depth = 1;
  while (depth > 0 && !Check(TokenKind::kEof)) {
    if (CurrentToken().kind == TokenKind::kLParen)
      depth++;
    else if (CurrentToken().kind == TokenKind::kRParen)
      depth--;
    if (depth > 0) Consume();
  }
  if (Check(TokenKind::kRParen)) Consume();
}

void Parser::SkipBracketedDims() {
  while (Check(TokenKind::kLBracket)) {
    Consume();
    int depth = 1;
    while (depth > 0 && !Check(TokenKind::kEof)) {
      if (CurrentToken().kind == TokenKind::kLBracket)
        depth++;
      else if (CurrentToken().kind == TokenKind::kRBracket)
        depth--;
      if (depth > 0) Consume();
    }
    if (Check(TokenKind::kRBracket)) Consume();
  }
}

bool Parser::TryInterfacePortTypedef(ModuleItem* item) {
  if (!CheckIdentifier()) return false;
  auto saved = lexer_.SavePos();
  Consume();
  SkipBracketedDims();
  if (!Check(TokenKind::kDot)) {
    lexer_.RestorePos(saved);
    return false;
  }
  lexer_.RestorePos(saved);
  item->typedef_ifc_port = Consume().text;
  while (Check(TokenKind::kLBracket)) {
    Consume();
    item->unpacked_dims.push_back(ParseExpr());
    Expect(TokenKind::kRBracket, Subclause("6.18"));
  }
  Expect(TokenKind::kDot, Subclause("6.18"));
  item->typedef_type.kind = DataTypeKind::kNamed;
  item->typedef_type.type_name =
      Expect(TokenKind::kIdentifier, Subclause("6.18")).text;
  item->name = Expect(TokenKind::kIdentifier, Subclause("6.18")).text;
  known_types_.insert(item->name);
  Expect(TokenKind::kSemicolon, Subclause("6.18"));
  return true;
}

DataType ParserDataDeclHelpers::ReadDeclaredTypeOfAName(Parser& p) {
  if (p.Check(TokenKind::kKwEnum)) return p.ParseEnumType();
  DataType dtype;
  if (p.Check(TokenKind::kKwStruct) || p.Check(TokenKind::kKwUnion)) {
    dtype = p.ParseStructOrUnionType();
    p.ParsePackedDims(dtype);
  } else if (!ReadTypeReference(p, dtype)) {
    dtype = p.ParseDeclaredDataType();
  }
  return dtype;
}

ModuleItem* Parser::ParseTypedef() {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kTypedef;
  item->loc = CurrentLoc();
  Expect(TokenKind::kKwTypedef, Subclause("6.18"));

  if (TryForwardClassTypedef(item)) return item;
  if (TryForwardAggregateTypedef(item)) return item;
  if (TryForwardBareTypedef(item)) return item;
  if (TryInterfacePortTypedef(item)) return item;

  item->typedef_type = ParserDataDeclHelpers::ReadDeclaredTypeOfAName(*this);

  item->name = Expect(TokenKind::kIdentifier, Subclause("6.18")).text;
  ParseUnpackedDims(item->unpacked_dims);
  known_types_.insert(item->name);
  Expect(TokenKind::kSemicolon, Subclause("6.18"));
  return item;
}

static const DataType* NettypeResolveScope(const DataType& path, Arena& arena) {
  if (path.scope_name.empty()) return nullptr;
  auto* scope = arena.Create<DataType>();
  scope->kind = DataTypeKind::kNamed;
  scope->type_name = path.scope_name;
  if (!path.outer_scope_names.empty()) {
    scope->scope_name = path.outer_scope_names.back();
    scope->outer_scope_names.assign(path.outer_scope_names.begin(),
                                    path.outer_scope_names.end() - 1);
  }
  if (path.scope_param_assignment_written) {
    scope->type_params = path.type_params;
  }
  return scope;
}

ModuleItem* Parser::ParseNettypeDecl() {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kNettypeDecl;
  item->loc = CurrentLoc();
  Expect(TokenKind::kKwNettype, Subclause("6.6.7"));
  item->typedef_type = ParserDataDeclHelpers::ReadDeclaredTypeOfAName(*this);
  item->name = Expect(TokenKind::kIdentifier, Subclause("6.6.7")).text;

  if (item->typedef_type.kind == DataTypeKind::kImplicit &&
      item->typedef_type.type_name.empty() &&
      item->typedef_type.type_ref_expr == nullptr) {
    diag_.Error(item->loc, "nettype declaration requires an explicit data type",
                Subclause("6.6.7"));
  }

  if (Match(TokenKind::kKwWith)) ParseNettypeWithClause(item);
  known_types_.insert(item->name);
  known_nettypes_.insert(item->name);
  Expect(TokenKind::kSemicolon, Subclause("6.6.7"));
  return item;
}

void Parser::ParseNettypeWithClause(ModuleItem* item) {
  const bool kUnitScope =
      Check(TokenKind::kSystemIdentifier) && CurrentToken().text == "$unit";
  if (!kUnitScope && !CheckIdentifier()) {
    Expect(TokenKind::kIdentifier, Subclause("6.6.7"));
    return;
  }
  DataType path = ParseNamedType();
  if (path.type_name == "$unit") {
    const TokenKind kMissing = Match(TokenKind::kColonColon)
                                   ? TokenKind::kIdentifier
                                   : TokenKind::kColonColon;
    Expect(kMissing, Subclause("A.2.1.3"));
  }
  item->nettype_resolve_func = path.type_name;
  item->nettype_resolve_scope = NettypeResolveScope(path, arena_);
}

Direction Parser::ParseArgDirection(FunctionArg& arg, Direction sticky_dir,
                                    bool* was_explicit) {
  if (was_explicit) *was_explicit = true;
  auto reject_extra_direction = [&](Direction first) {
    while (IsDirectionQualifierKw(CurrentToken().kind)) {
      bool involves_ref = first == Direction::kRef || Check(TokenKind::kKwRef);
      if (!involves_ref) break;
      diag_.Error(CurrentLoc(),
                  "combining ref with another directional qualifier is "
                  "illegal",
                  Subclause("13.3"));
      Consume();
      Match(TokenKind::kKwStatic);
    }
  };
  if (Check(TokenKind::kKwInput)) {
    arg.direction = Direction::kInput;
    Consume();
    reject_extra_direction(Direction::kInput);
    return Direction::kInput;
  }
  if (Check(TokenKind::kKwOutput)) {
    arg.direction = Direction::kOutput;
    Consume();
    reject_extra_direction(Direction::kOutput);
    return Direction::kOutput;
  }
  if (Check(TokenKind::kKwInout)) {
    arg.direction = Direction::kInout;
    Consume();
    reject_extra_direction(Direction::kInout);
    return Direction::kInout;
  }
  if (Check(TokenKind::kKwRef)) {
    arg.direction = Direction::kRef;
    Consume();
    arg.is_ref_static = Match(TokenKind::kKwStatic);
    reject_extra_direction(Direction::kRef);
    return Direction::kRef;
  }
  arg.direction = sticky_dir;
  if (was_explicit) *was_explicit = false;
  return sticky_dir;
}

bool Parser::TryParseDefaultArgSentinel(std::vector<FunctionArg>& args,
                                        FuncArgScan& scan) {
  if (!Check(TokenKind::kKwDefault)) return false;
  if (!scan.constructor_args) {
    diag_.Error(CurrentLoc(),
                "a 'default' argument stands in a class constructor's "
                "argument list alone",
                Subclause("A.1.9"));
  }
  if (scan.seen_default) {
    diag_.Error(CurrentLoc(),
                "'default' already appears earlier in this class constructor "
                "argument list",
                Subclause("8.17"));
  }
  scan.seen_default = true;
  FunctionArg arg;
  arg.is_default = true;
  Consume();
  args.push_back(arg);
  scan.prev_was_default = true;
  return true;
}

void Parser::ParseFunctionArgTrailer(FunctionArg& arg,
                                     bool require_identifiers) {
  const bool kNamed = CheckIdentifier();
  if (kNamed) {
    arg.name = Consume().text;
  } else if (require_identifiers) {
    diag_.Error(CurrentLoc(),
                "tf_port_item shall include a port_identifier outside of a "
                "function_prototype or task_prototype",
                Subclause("13.3"));
  }
  if (!kNamed && !require_identifiers &&
      (Check(TokenKind::kLBracket) || Check(TokenKind::kEq))) {
    diag_.Error(CurrentLoc(),
                "a formal written without a name takes no unpacked dimension "
                "and no default value",
                Subclause("A.2.7"));
  }
  ParseUnpackedDims(arg.unpacked_dims);
  if (Match(TokenKind::kEq)) {
    arg.default_value = ParseExpr();
  }
}

void Parser::ParseOneFunctionArg(std::vector<FunctionArg>& args,
                                 FuncArgScan& scan, bool require_identifiers) {
  if (Check(TokenKind::kAttrStart)) {
    ParseAttributes();
  }

  if (TryParseDefaultArgSentinel(args, scan)) return;

  FunctionArg arg;
  if (Check(TokenKind::kKwConst)) {
    const SourceLoc kConstLoc = CurrentLoc();
    Consume();
    arg.is_const = Check(TokenKind::kKwRef);
    if (!arg.is_const) {
      diag_.Error(kConstLoc,
                  "'const' in a formal qualifies only a 'ref' direction",
                  Subclause("A.2.7"));
    }
  }
  if (scan.prev_was_default) scan.sticky_dir = Direction::kInput;
  bool dir_explicit = false;
  scan.sticky_dir = ParseArgDirection(arg, scan.sticky_dir, &dir_explicit);

  InheritRefQualifiers(args, arg, dir_explicit);
  bool has_var = Match(TokenKind::kKwVar);
  if (!ParserDataDeclHelpers::ReadKeyedTypeReference(*this, arg.data_type,
                                                     has_var, false) &&
      !TryParseInlineAggregateType(arg.data_type)) {
    arg.data_type = ParseDeclaredDataType();
  }
  if (arg.data_type.kind == DataTypeKind::kImplicit &&
      arg.data_type.packed_dim_left == nullptr && Check(TokenKind::kLBracket)) {
    ParsePackedDims(arg.data_type);
  }
  ResolveImplicitArgDataType(arg, scan.prev_data_type, dir_explicit,
                             scan.first_arg, scan.prev_was_default);

  ParseFunctionArgTrailer(arg, require_identifiers);
  scan.prev_data_type = arg.data_type;
  scan.first_arg = false;
  scan.prev_was_default = false;
  args.push_back(arg);
}

std::vector<FunctionArg> Parser::ParseFunctionArgs(bool require_identifiers,
                                                   bool constructor_args) {
  std::vector<FunctionArg> args;
  Expect(TokenKind::kLParen, Subclause("13.3"));
  if (Check(TokenKind::kRParen)) {
    Consume();
    return args;
  }
  FuncArgScan scan;
  scan.constructor_args = constructor_args;
  do {
    ParseOneFunctionArg(args, scan, require_identifiers);
  } while (Match(TokenKind::kComma));
  Expect(TokenKind::kRParen, Subclause("13.3"));
  return args;
}

DataType Parser::ParseFunctionReturnType() {
  if (Check(TokenKind::kKwVoid)) {
    DataType dt;
    dt.kind = DataTypeKind::kVoid;
    Consume();
    return dt;
  }
  if (Check(TokenKind::kLBracket)) {
    DataType dt;
    ParsePackedDims(dt);
    return dt;
  }
  DataType dt;
  if (TryParseInlineAggregateType(dt)) {
    return dt;
  }
  if (Check(TokenKind::kKwType)) {
    Consume();
    Expect(TokenKind::kLParen, Subclause("6.23"));
    dt.type_ref_expr = ParseExpr();
    Expect(TokenKind::kRParen, Subclause("6.23"));
    return dt;
  }
  return ParseDeclaredDataType();
}

bool Parser::TryParseInlineAggregateType(DataType& dt) {
  if (Check(TokenKind::kKwEnum)) {
    dt = ParseEnumType();
    return true;
  }
  if (Check(TokenKind::kKwStruct) || Check(TokenKind::kKwUnion)) {
    dt = ParseStructOrUnionType();
    ParsePackedDims(dt);
    return true;
  }
  return false;
}

static void RejectStaticOutOfBlockMethod(const ModuleItem* item,
                                         DiagEngine& diag) {
  if (item->is_static) {
    diag.Error(item->loc, "class method shall not have static lifetime",
               Subclause("8.6"));
  }
}

static bool MovedPastLoc(SourceLoc before, SourceLoc after) {
  return before.file_id != after.file_id || before.line != after.line ||
         before.column != after.column;
}

static void RejectConstructorReturnType(ModuleItem* item, SourceLoc type_loc,
                                        DiagEngine& diag) {
  if (item->name != "new") return;
  diag.Error(type_loc,
             "'new' is declared with a return type here, which a constructor "
             "never has",
             Subclause("8.7"));
  item->return_type = DataType{};
}

static void RejectInterfacePrefixAfterClassScope(const ModuleItem* item,
                                                 bool dot_follows,
                                                 SourceLoc dot_loc,
                                                 DiagEngine& diag) {
  if (item->method_class.empty() || !dot_follows) return;
  diag.Error(dot_loc,
             "a function's name takes an interface prefix or a class scope, "
             "not both",
             Subclause("A.2.6"));
}

void Parser::ParseFuncName(ModuleItem* item) {
  if (Check(TokenKind::kKwNew)) {
    item->name = "new";
    Consume();
    item->return_type = DataType{};
    return;
  }

  const SourceLoc kTypeLoc = CurrentLoc();
  item->return_type = ParseFunctionReturnType();
  bool type_written = MovedPastLoc(kTypeLoc, CurrentLoc());

  if (item->return_type.kind == DataTypeKind::kNamed &&
      Check(TokenKind::kColonColon)) {
    item->method_class = item->return_type.type_name;
    item->return_type = DataType{};
    type_written = false;
    Consume();
    item->name = Match(TokenKind::kKwNew)
                     ? "new"
                     : Expect(TokenKind::kIdentifier, Subclause("8.24")).text;
  } else {
    item->name = Match(TokenKind::kKwNew)
                     ? "new"
                     : Expect(TokenKind::kIdentifier, Subclause("13.4")).text;
  }

  while (Match(TokenKind::kColonColon)) {
    item->method_class = item->name;
    item->name = Match(TokenKind::kKwNew)
                     ? "new"
                     : Expect(TokenKind::kIdentifier, Subclause("8.24")).text;
  }
  if (!item->method_class.empty()) RejectStaticOutOfBlockMethod(item, diag_);
  if (type_written) RejectConstructorReturnType(item, kTypeLoc, diag_);

  RejectInterfacePrefixAfterClassScope(item, Check(TokenKind::kDot),
                                       CurrentLoc(), diag_);
  if (Match(TokenKind::kDot)) {
    item->method_class = item->name;
    item->name = Expect(TokenKind::kIdentifier, Subclause("25.7")).text;
  }
}

void Parser::ParseFuncBody(ModuleItem* item) {
  ParseSubroutineBody(item, TokenKind::kKwEndfunction, Subclause("13.4"));
  Expect(TokenKind::kKwEndfunction, Subclause("13.4"));
  if (Match(TokenKind::kColon)) {
    std::string_view end_name;
    SourceLoc end_loc = CurrentLoc();
    if (Match(TokenKind::kKwNew)) {
      end_name = "new";
    } else {
      auto end_id = ExpectIdentifier(Subclause("9.3.4"));
      end_name = end_id.text;
      end_loc = end_id.loc;
    }
    if (end_name != item->name) {
      diag_.Error(end_loc,
                  "end label '" + std::string(end_name) + "' does not match '" +
                      std::string(item->name) + "'",
                  Subclause("9.3.4"));
    }
  }
}

ModuleItem* Parser::ParseFunctionDecl(bool prototype_only) {
  TypeNameScope type_scope(*this);
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kFunctionDecl;
  item->loc = CurrentLoc();
  Expect(TokenKind::kKwFunction, Subclause("13.4"));

  ParseDynamicOverrideSpecifiers(item);

  item->is_automatic = Match(TokenKind::kKwAutomatic);
  if (!item->is_automatic) item->is_static = Match(TokenKind::kKwStatic);

  ParseFuncName(item);
  if (!item->method_class.empty())
    AdoptMethodClassTypeNames(item->method_class);

  if (Check(TokenKind::kLParen)) {
    item->func_args = ParseFunctionArgs(!prototype_only, item->name == "new");
    item->is_ansi_ports = true;
  }
  Expect(TokenKind::kSemicolon, Subclause("13.4"));

  if (!prototype_only) ParseFuncBody(item);
  return item;
}

ModuleItem* Parser::ParseTaskDecl(bool prototype_only) {
  TypeNameScope type_scope(*this);
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kTaskDecl;
  item->loc = CurrentLoc();
  Expect(TokenKind::kKwTask, Subclause("13.3"));

  ParseDynamicOverrideSpecifiers(item);

  if (Match(TokenKind::kKwAutomatic)) {
    item->is_automatic = true;
  } else if (Match(TokenKind::kKwStatic)) {
    item->is_static = true;
  }

  item->name = Expect(TokenKind::kIdentifier, Subclause("13.3")).text;

  const bool kInterfacePrefixed = Match(TokenKind::kDot);
  if (kInterfacePrefixed) {
    item->method_class = item->name;
    item->name = Expect(TokenKind::kIdentifier, Subclause("25.7")).text;
  }

  if (kInterfacePrefixed && Check(TokenKind::kColonColon)) {
    diag_.Error(
        CurrentLoc(),
        "a task's name takes an interface prefix or a class scope, not both",
        Subclause("A.2.7"));
  }
  bool class_scoped = false;
  while (Match(TokenKind::kColonColon)) {
    item->method_class = item->name;
    item->name = Expect(TokenKind::kIdentifier, Subclause("8.24")).text;
    class_scoped = true;
  }
  if (class_scoped) RejectStaticOutOfBlockMethod(item, diag_);
  if (!item->method_class.empty())
    AdoptMethodClassTypeNames(item->method_class);

  if (Check(TokenKind::kLParen)) {
    item->func_args = ParseFunctionArgs(!prototype_only);
    item->is_ansi_ports = true;
  }
  Expect(TokenKind::kSemicolon, Subclause("13.3"));

  if (prototype_only) return item;

  ParseSubroutineBody(item, TokenKind::kKwEndtask, Subclause("13.3"));
  Expect(TokenKind::kKwEndtask, Subclause("13.3"));
  MatchEndLabel(item->name);
  return item;
}

static int NestingStep(TokenKind k) {
  if (k == TokenKind::kLParen || k == TokenKind::kLBracket ||
      k == TokenKind::kLBrace) {
    return 1;
  }
  if (k == TokenKind::kRParen || k == TokenKind::kRBracket ||
      k == TokenKind::kRBrace) {
    return -1;
  }
  return 0;
}

bool Parser::OpensEventGroup(bool edges_only) {
  auto saved = lexer_.SavePos();
  Consume();
  bool group = false;
  bool opens_event = true;
  for (int depth = 0; !group && depth >= 0 && !Check(TokenKind::kEof);
       Consume()) {
    const TokenKind kKind = CurrentToken().kind;
    const bool kSeparates =
        depth == 0 && (kKind == TokenKind::kKwOr || kKind == TokenKind::kComma);
    const bool kOpensEvent =
        opens_event &&
        (kKind == TokenKind::kKwPosedge || kKind == TokenKind::kKwNegedge ||
         kKind == TokenKind::kKwEdge ||
         (kKind == TokenKind::kLParen && OpensEventGroup(edges_only)));
    group = kOpensEvent ||
            (!edges_only &&
             (kSeparates || (depth == 0 && kKind == TokenKind::kKwIff)));
    opens_event = kSeparates;
    depth += NestingStep(kKind);
  }
  lexer_.RestorePos(saved);
  return group;
}

std::vector<EventExpr> Parser::ParseEventList() {
  std::vector<EventExpr> events;
  auto parse_event_or_group = [&]() {
    if (Check(TokenKind::kLParen) && OpensEventGroup(false)) {
      Consume();
      auto sub = ParseEventList();
      events.insert(events.end(), sub.begin(), sub.end());
      Expect(TokenKind::kRParen, Subclause("9.4.2"));
      return;
    }
    events.push_back(ParseSingleEvent());
  };
  parse_event_or_group();
  while (Match(TokenKind::kKwOr) || Match(TokenKind::kComma)) {
    parse_event_or_group();
  }
  return events;
}

EventExpr Parser::ParseSingleEvent() {
  EventExpr ev;
  if (Match(TokenKind::kKwPosedge)) {
    ev.edge = Edge::kPosedge;
  } else if (Match(TokenKind::kKwNegedge)) {
    ev.edge = Edge::kNegedge;
  } else if (Match(TokenKind::kKwEdge)) {
    ev.edge = Edge::kEdge;
  }
  ev.signal = ParseExpr();

  if (Match(TokenKind::kKwIff)) {
    ev.iff_condition = ParseExpr();
  }
  return ev;
}

}  // namespace delta
