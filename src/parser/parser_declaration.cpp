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

// §8.17: a tf_port_item with no explicit direction that is 'ref' inherits the
// const/static qualifiers of the immediately preceding 'ref' argument. Operates
// purely on already-parsed argument state (no lexer access).
void InheritRefQualifiers(const std::vector<FunctionArg>& args,
                          FunctionArg& arg, bool dir_explicit) {
  if (dir_explicit || arg.direction != Direction::kRef || args.empty()) return;
  const auto& prev = args.back();
  if (prev.direction != Direction::kRef) return;
  arg.is_const = arg.is_const || prev.is_const;
  arg.is_ref_static = arg.is_ref_static || prev.is_ref_static;
}

// §8.17: resolve an implicit tf_port data type — the first argument and any
// argument with an explicit direction (or following 'default') default to
// logic; otherwise it inherits the previous argument's data type. Pure state
// update.
//
// §13.3 (printed page 336): the implicit form of a tf_port_item's type is a
// signing and packed dimensions with no type keyword, and a formal whose
// data type is not declared is `logic`, so `input [7:0] a` is a logic vector
// of the written dimension rather than a formal of no type carrying one --
// the simulator sizes a formal by its declared type and left the actual's
// nine bits in an eight-bit formal -- and the `b` that inherits from it
// (printed page 337, mytask4) inherits `logic [7:0]`.
void ResolveImplicitArgDataType(FunctionArg& arg,
                                const DataType& prev_data_type,
                                bool dir_explicit, bool first_arg,
                                bool prev_was_default) {
  // A type reference is no implicit type, whatever its kind until the
  // elaborator resolves it (§6.23).
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

// §6.18 forward-typedef discriminator: the DataTypeKind named by a leading
// enum/struct/union keyword, or kImplicit for any other token.
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

// §6.18: enum/struct/union introduce a forward-typedef aggregate kind.
bool IsAggregateKw(TokenKind tk) {
  return tk == TokenKind::kKwEnum || tk == TokenKind::kKwStruct ||
         tk == TokenKind::kKwUnion;
}

// §13.3: any directional qualifier keyword (used to detect an illegal second
// qualifier after a ref/direction has already been parsed).
bool IsDirectionQualifierKw(TokenKind tk) {
  return tk == TokenKind::kKwRef || tk == TokenKind::kKwInput ||
         tk == TokenKind::kKwOutput || tk == TokenKind::kKwInout;
}

}  // namespace

// A.9.3: whether `target`, a defparam's, is a hierarchical_identifier: names
// joined by `.`, each but the last with any constant bit-selects, the first
// alone or behind `$root .`. A package or class scope, `p::P`, joins none.
static bool IsHierarchicalParameterName(const Expr* target) {
  while (target->kind == ExprKind::kMemberAccess &&
         !target->is_scope_resolution) {
    target = target->lhs;
    while (target->kind == ExprKind::kSelect) target = target->base;
  }
  return target->kind == ExprKind::kIdentifier &&
         (target->scope_prefix.empty() || target->scope_prefix == "$root");
}

// A.2.4's defparam_assignment is a hierarchical_parameter_identifier, `=` and
// a constant_mintypmax_expression. A target written as any other expression
// is reported, and read whole so the value after it still parses.
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

// Forward class/interface typedef: `typedef class foo;` (§6.18).
bool Parser::TryForwardClassTypedef(ModuleItem* item) {
  if (!Check(TokenKind::kKwClass) && !Check(TokenKind::kKwInterface)) {
    return false;
  }
  Consume();
  if (Check(TokenKind::kKwClass)) Consume();
  item->name = Expect(TokenKind::kIdentifier, Subclause("6.18")).text;
  // §6.18: record that this forward declaration specified the class (or
  // interface class) basic type, so the elaborator can reject a later
  // definition of the same name that does not resolve to a class. A class type
  // is always referenced by name, so kNamed is the recorded forward kind.
  item->forward_type_kind = DataTypeKind::kNamed;
  known_types_.insert(item->name);
  Expect(TokenKind::kSemicolon, Subclause("6.18"));
  return true;
}

// Forward enum/struct/union typedef: `typedef struct foo;` (§6.18). Leaves the
// lexer position unchanged when the form does not match.
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

// Forward bare typedef: `typedef foo;` (§6.18).
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

// Skip a (possibly nested) run of bracketed unpacked-dimension tokens while
// probing for the interface-port '.'-form.
// Consumes a balanced `( ... )` group when the cursor is on the opening paren;
// a no-op otherwise. Used for lookahead past a parameter value list.
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

// Interface-port typedef: `typedef intf.T name;` (§6.18).
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
    // A.2.2.1 lets packed dimensions follow the body, making the type a packed
    // array of the structure or union (§7.4.1).
    dtype = p.ParseStructOrUnionType();
    p.ParsePackedDims(dtype);
  } else if (!ReadTypeReference(p, dtype)) {
    // A.2.2.1 counts a type_reference among the data types, so §6.23's
    // `typedef type(x) t;` names the type of x, which the elaborator resolves.
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

  // A.2.1.3's type_declaration takes a data_type, and A.2.2.1 admits a
  // type_identifier behind a package_scope or a class_scope, the `r::` of
  // `typedef r::real_holder_t idx_t;` reaching the package's typedef by §26.3
  // (printed page 808). ParseDeclaredDataType reads such a name past
  // known_types_, where a package name never stands; ParseDataType left `r`
  // to be read as the typedef's own name, the `::` after it reported as a
  // missing semicolon under §6.18, and `r` then recorded as a forward typedef
  // no definition resolves. The forward forms above are already settled by
  // the time this is reached, so `typedef T;` stays a forward typedef.
  item->typedef_type = ParserDataDeclHelpers::ReadDeclaredTypeOfAName(*this);

  item->name = Expect(TokenKind::kIdentifier, Subclause("6.18")).text;
  ParseUnpackedDims(item->unpacked_dims);
  known_types_.insert(item->name);
  Expect(TokenKind::kSemicolon, Subclause("6.18"));
  return item;
}

// The scope a nettype's with clause names its resolution function through,
// read from the whole name `path` ParseNamedType gave the clause: the names
// before the function's, the last of them as type_name. ParseNamedType keeps a
// parameter_value_assignment in type_params, and scope_param_assignment_written
// says the class before the last name was written with it. Null when the
// function was named alone.
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
  // A.2.2.1's data_type and A.2.1.3's second form, which renames a nettype, may
  // each name the type through a package, `P::T`, whose name is no type the
  // parser knows, and the data_type may write an enumeration, a structure or a
  // union out in full, as a typedef's may (§6.6.7 admits packed and unpacked
  // aggregates alike). A.2.2.1 counts a type_reference among the data types,
  // so `nettype type(x) nt;` names the type of x (§6.23).
  item->typedef_type = ParserDataDeclHelpers::ReadDeclaredTypeOfAName(*this);
  item->name = Expect(TokenKind::kIdentifier, Subclause("6.6.7")).text;

  // §6.6.7 / A.2.1.3: a nettype declaration requires an explicit data type
  // (or a source nettype). A lone `nettype name;` is not well formed.
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

// A.2.1.3 with A.2.2.1: `with [ package_scope | class_scope ] tf_identifier`,
// read from after `with`. A package_scope is a package name or `$unit`, then
// `::`, and a class_scope a class_type, then `::`: a class name with an
// optional parameter_value_assignment, named through a package_scope and
// followed by the names of the classes nested in it, each with its own.
// ParseNamedType reads that chain as it reads a scoped type's name, so the name
// it ends at is the function's and the names before are its scope. The scope
// is kept, since `with C::res` and `with res` name different functions.
void Parser::ParseNettypeWithClause(ModuleItem* item) {
  const bool kUnitScope =
      Check(TokenKind::kSystemIdentifier) && CurrentToken().text == "$unit";
  if (!kUnitScope && !CheckIdentifier()) {
    Expect(TokenKind::kIdentifier, Subclause("6.6.7"));
    return;
  }
  DataType path = ParseNamedType();
  // `$unit` opens a package_scope and never names the function itself.
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

// §8.17: the 'default' sentinel in a class constructor argument list. Records
// a default placeholder argument; returns true when consumed so the caller
// skips to the next argument. A.1.9 gives the sentinel to
// class_constructor_arg alone -- `class_constructor_arg ::= tf_port_item |
// default` -- where A.2.7's tf_port_item, the argument of every other task and
// function, has no such form, so one in another subroutine's list is reported
// and still recorded.
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

// tf_port_item trailer: the port identifier, unpacked dimensions, and an
// optional default value (§13.3 / §8.17).
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
  // A.2.7 writes the unpacked dimensions and the default value inside the
  // optional group the port_identifier opens, so a prototype's formal written
  // without a name has neither. Each is still read, so the list goes on.
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

// Parse one tf_port_item and append it to args, advancing the carried scan
// state (sticky direction, default/data-type inheritance per §8.17/§13.3).
void Parser::ParseOneFunctionArg(std::vector<FunctionArg>& args,
                                 FuncArgScan& scan, bool require_identifiers) {
  // tf_port_item permits a leading attribute_instance list; consume and
  // discard any such list before the rest of the port item.
  if (Check(TokenKind::kAttrStart)) {
    ParseAttributes();
  }

  if (TryParseDefaultArgSentinel(args, scan)) return;

  FunctionArg arg;
  // A.2.7's tf_port_direction writes `const` only before `ref`, as
  // `[ const ] ref [ static ]`, so a `const` that no `ref` follows is reported
  // and the formal read as if it were not there.
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
  // §8.17: the argument following 'default' starts from the default direction
  // (input) rather than inheriting the previous argument's direction via
  // stickiness.
  if (scan.prev_was_default) scan.sticky_dir = Direction::kInput;
  bool dir_explicit = false;
  scan.sticky_dir = ParseArgDirection(arg, scan.sticky_dir, &dir_explicit);

  InheritRefQualifiers(args, arg, dir_explicit);
  bool has_var = Match(TokenKind::kKwVar);
  // A.2.2.1's data_type lets a type_identifier stand behind a package_scope
  // (§26.3), so `ref p::pair_t x` reads the scoped type as a declaration's
  // does. It may be a type_reference too, which a formal, a variable of the
  // subroutine, writes after `var` (§6.23).
  if (!ParserDataDeclHelpers::ReadKeyedTypeReference(*this, arg.data_type,
                                                     has_var, false) &&
      !TryParseInlineAggregateType(arg.data_type)) {
    arg.data_type = ParseDeclaredDataType();
  }
  // A.2.7's tf_port_item takes a data_type_or_implicit, and A.2.2.1's
  // implicit_data_type is `[ signing ] { packed_dimension }`: a port written
  // `input [W-1:0] fbv3` (§H.11.1's Example 4) names no type and no signing
  // and carries its packed dimensions alone, which ParseDataType leaves
  // unread when nothing precedes them.
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
  // §8.17: an argument that directly follows the 'default' keyword in a
  // constructor argument list does not inherit the preceding argument's
  // direction or data type; it falls back to the default direction (input) and
  // default data type (logic). That carried state lives in FuncArgScan.
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
  // §6.23: a type_reference (e.g. `type(this)`) is a valid return type.
  if (Check(TokenKind::kKwType)) {
    Consume();
    Expect(TokenKind::kLParen, Subclause("6.23"));
    dt.type_ref_expr = ParseExpr();
    Expect(TokenKind::kRParen, Subclause("6.23"));
    return dt;
  }
  // A.2.7's function_data_type_or_implicit takes a data_type, which A.2.2.1
  // lets stand behind a package_scope, so `function pk::t f();` reads the
  // scoped type; `function C::f();` of an out-of-block declaration, whose
  // class this parse may not know, is left to ParseDataType and the name walk
  // in ParseFuncName.
  return ParseDeclaredDataType();
}

bool Parser::TryParseInlineAggregateType(DataType& dt) {
  // ParseDataType() does not handle the struct/union/enum keywords, so dispatch
  // them here as every data-type caller must. Without this, an inline aggregate
  // type (e.g. a `struct {...}` DPI import argument or function return type)
  // left the cursor on the keyword, derailing the surrounding parse.
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

// §8.6 with §8.24: a body written `C::f` outside its class is the class's
// method, which takes no static lifetime, as Parser::ValidateClassMethod
// reports of one written in the class.
static void RejectStaticOutOfBlockMethod(const ModuleItem* item,
                                         DiagEngine& diag) {
  if (item->is_static) {
    diag.Error(item->loc, "class method shall not have static lifetime",
               Subclause("8.6"));
  }
}

// Whether the token current at `after` stands elsewhere than the one current
// at `before`, which is whether reading between them consumed a token. The
// lexer's own saved position cannot say: a token already peeked has moved it
// before the token is consumed.
static bool MovedPastLoc(SourceLoc before, SourceLoc after) {
  return before.file_id != after.file_id || before.line != after.line ||
         before.column != after.column;
}

// §8.7 defines `new` as a function with no return type, and A.1.9's
// class_constructor_declaration and class_constructor_prototype write none
// between `function` and `new`. A type written there, at `type_loc`, is
// reported and dropped, so the constructor reads as it would have without one.
static void RejectConstructorReturnType(ModuleItem* item, SourceLoc type_loc,
                                        DiagEngine& diag) {
  if (item->name != "new") return;
  diag.Error(type_loc,
             "'new' is declared with a return type here, which a constructor "
             "never has",
             Subclause("8.7"));
  item->return_type = DataType{};
}

// A.2.6 writes a function_body_declaration's name as
// `[ interface_identifier . | class_scope ] function_identifier`, one prefix
// or the other, so a `.` at `dot_loc` after the class scope `item` was named
// in is reported; the caller still reads the interface prefix it opens.
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

  // A class this parse does not know, `Other` in `function Other::new();`, is
  // read as no type at all and left for the name walk below, so a return type
  // was written only where the reader moved past a token.
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
  // §23.9 makes a function a scope, so a typedef in its body is not a type name
  // after `endfunction`. The guard opens before the tf_port_list rather than in
  // ParseFuncBody, because §13.4 declares the formal arguments in the
  // function's own scope too.
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
  // §23.9 makes a task a scope, and §13.3 declares its formal arguments in it,
  // so the guard opens before the tf_port_list exactly as ParseFunctionDecl's
  // does.
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

  // A.2.7 writes `[ interface_identifier . | class_scope ] task_identifier`,
  // one prefix or the other, so a class scope after an interface prefix is
  // reported and still read.
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

// The change in nesting depth a token makes.
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

// §9.4 Syntax 9-4: an event_expression may be a parenthesized one, and an
// expression may be parenthesized too, so the `(` alone does not say which it
// opens. A group opens with an edge keyword or with a group of its own, or
// holds an `or`, a `,` or an `iff` at its own level of nesting, none of which
// an expression holds there; anything else in the parentheses is an
// expression. Where the parentheses may hold a sequence or a property as
// well, an actual argument (footnote 36 to Syntax 9-4), `edges_only` asks
// for the reading that settles it: an `or`, a `,` or an `iff` may join a
// sequence's or a property's operands too, so the group is one only where an
// edge keyword, or a group of its own that is one, opens an event at its own
// level of nesting, first or after a `,` or an `or`, which no operand of
// either opens with. The tokens are scanned to the matching `)` and the
// position is restored.
bool Parser::OpensEventGroup(bool edges_only) {
  auto saved = lexer_.SavePos();
  Consume();  // (
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
