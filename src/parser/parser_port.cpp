#include <cctype>
#include <format>
#include <optional>
#include <string_view>

#include "common/types.h"
#include "parser/parser.h"

namespace delta {

static bool IsValidCIdentifier(std::string_view text) {
  if (text.empty()) return false;
  auto first = static_cast<unsigned char>(text.front());
  if (!std::isalpha(first) && first != '_') return false;
  for (char ch : text.substr(1)) {
    auto c = static_cast<unsigned char>(ch);
    if (!std::isalnum(c) && c != '_') return false;
  }
  return true;
}

// §35.5.4: dpi_spec_string ::= "DPI-C" | "DPI". The lexer keeps the raw
// quoted text in the token; this returns the inner characters so the rest
// of the parser can compare against the two literal values from Syntax 35-1.
static std::string_view StripStringLiteralQuotes(std::string_view text) {
  if (text.size() < 2) return text;
  if (text.front() != '"' || text.back() != '"') return text;
  return text.substr(1, text.size() - 2);
}

static void ResolvePortDefaults(PortDecl& port, const PortDecl* prev,
                                bool is_checker);

// §23.10 / Syntax A.1.3 parameter_port_list: the collections being built up as
// each parameter_declaration / type_parameter_declaration in the list is
// parsed. These four references are the one accumulator object for the whole
// parameter port list, so the value- and type-parameter parsers share it.
struct ParamPortList {
  std::vector<std::pair<std::string_view, Expr*>>& params;
  std::unordered_set<std::string_view>& type_param_names;
  std::unordered_set<std::string_view>& localparam_port_names;
  std::vector<DataType>* param_types;
};

// CPD-dedup: the dpi_spec_string parse/validation and the optional
// "= c_identifier" tail are identical between DPI import and export.
struct ParserPortHelpers {
  static void ParseDpiSpecString(Parser& p, ModuleItem* item) {
    auto spec_tok = p.Consume();
    item->dpi_spec_string = StripStringLiteralQuotes(spec_tok.text);
    if (item->dpi_spec_string == "DPI") {
      // §35.5.4: "DPI" is deprecated; the warning text must point at the
      // canonical replacement and warn about possible C-code changes.
      p.diag_.Warning(
          spec_tok.loc,
          "\"DPI\" is deprecated and should be replaced with \"DPI-C\"; "
          "use of the \"DPI-C\" string may require changes to the DPI "
          "application's C code");
    } else if (item->dpi_spec_string != "DPI-C") {
      p.diag_.Error(spec_tok.loc,
                    "DPI specification string must be \"DPI-C\" or \"DPI\"");
    }
  }

  static void TryParseDpiCName(Parser& p, ModuleItem* item) {
    if (p.Check(TokenKind::kIdentifier)) {
      auto saved = p.lexer_.SavePos();
      auto tok = p.Consume();
      if (p.Match(TokenKind::kEq)) {
        if (!IsValidCIdentifier(tok.text)) {
          p.diag_.Error(tok.loc,
                        "DPI c_identifier must match [a-zA-Z_][a-zA-Z0-9_]*");
        }
        item->dpi_c_name = tok.text;
      } else {
        p.lexer_.RestorePos(saved);
      }
    }
  }

  // Apply one non-ANSI body port declaration (a single name + dims) to the
  // matching already-declared port(s), reporting a duplicate-direction error.
  static void ApplyNonAnsiPortDecl(Parser& p, ModuleDecl& mod, Direction dir,
                                   const DataType& dtype) {
    auto loc = p.CurrentLoc();
    auto name = p.Expect(TokenKind::kIdentifier).text;
    std::vector<Expr*> dims;
    p.ParseUnpackedDims(dims);
    bool found = false;
    for (auto& port : mod.ports) {
      if (port.name != name) continue;

      if (!found && port.direction != Direction::kNone) {
        p.diag_.Error(loc,
                      std::format("duplicate port declaration for '{}'", name));
      }
      found = true;
      port.direction = dir;
      port.data_type = dtype;
      port.unpacked_dims = dims;
    }
  }

  // Parse a single non-ANSI list_of_ports bit-/part-select on a bare port name
  // (`name[idx]` / `name[msb:lsb]`), captured as a select port_expr.
  static Expr* ParseNonAnsiPortSelect(Parser& p, std::string_view name) {
    auto* ref = p.arena_.Create<Expr>();
    ref->kind = ExprKind::kIdentifier;
    ref->text = name;
    p.Consume();
    auto* idx = p.ParseExpr();
    auto* sel = p.arena_.Create<Expr>();
    sel->kind = ExprKind::kSelect;
    sel->base = ref;
    sel->index = idx;
    if (p.Match(TokenKind::kColon)) {
      sel->index_end = p.ParseExpr();
    }
    p.Expect(TokenKind::kRBracket);
    return sel;
  }

  // Parse a single non-ANSI list_of_ports entry (.name(expr), {concat}, or a
  // bare name with an optional bit-/part-select).
  static PortDecl ParseNonAnsiPortEntry(Parser& p) {
    PortDecl port;
    port.loc = p.CurrentLoc();
    if (p.Match(TokenKind::kDot)) {
      port.is_explicit_named = true;
      port.name = p.ExpectIdentifier().text;
      p.Expect(TokenKind::kLParen);
      if (!p.Check(TokenKind::kRParen)) {
        port.port_expr = p.ParseExpr();
      }
      p.Expect(TokenKind::kRParen);
    } else if (p.Check(TokenKind::kLBrace)) {
      port.port_expr = p.ParseExpr();
    } else {
      port.name = p.ExpectIdentifier().text;
      if (p.Check(TokenKind::kLBracket)) {
        port.port_expr = ParseNonAnsiPortSelect(p, port.name);
      }
    }
    return port;
  }

  // §23.2.2.3: an ANSI `interface[.modport] name [dims] [= default]` port.
  // The `interface` keyword has already been peeked but not consumed.
  static void ParseAnsiInterfacePort(Parser& p, PortDecl& port) {
    p.Consume();
    port.is_interface_port = true;
    if (p.Match(TokenKind::kDot)) {
      port.data_type.modport_name = p.ExpectIdentifier().text;
    }
    port.name = p.ExpectIdentifier().text;
    p.ParseUnpackedDims(port.unpacked_dims);
    if (p.Match(TokenKind::kEq)) {
      port.default_value = p.ParseExpr();
    }
  }

  // After `iface_name.modport_name` has been recognized (both identifier
  // tokens consumed), fill in the named-interface-port fields and parse the
  // remaining `port_name [dims] [= default]` tail.
  static void FinishAnsiModportPort(Parser& p, PortDecl& port,
                                    std::string_view iface_name,
                                    std::string_view modport_name) {
    port.data_type.kind = DataTypeKind::kNamed;
    port.data_type.type_name = iface_name;
    port.data_type.modport_name = modport_name;
    port.name = p.ExpectIdentifier().text;
    p.ParseUnpackedDims(port.unpacked_dims);
    if (p.Match(TokenKind::kEq)) {
      port.default_value = p.ParseExpr();
    }
  }

  // Attempt to match `iface_name.modport_name port_name` from the current
  // position, consuming tokens as it goes. Returns true and fully parses the
  // port when the modport form is matched; returns false without restoring the
  // lexer (the caller is responsible for restoring the saved position).
  static bool TryMatchAnsiModportPort(Parser& p, PortDecl& port) {
    auto id_tok = p.Consume();
    if (!p.Check(TokenKind::kDot)) return false;
    p.Consume();
    if (!p.CheckIdentifier()) return false;
    auto modport_tok = p.Consume();
    if (!p.CheckIdentifier()) return false;
    FinishAnsiModportPort(p, port, id_tok.text, modport_tok.text);
    return true;
  }

  // Disambiguate `iface_name.modport_name port_name` (a named interface port
  // with an explicit modport) from an ordinary typed port. Returns true and
  // fully parses the port when the modport form is matched; otherwise restores
  // the lexer position and returns false so the caller parses a data type.
  static bool TryParseAnsiModportPort(Parser& p, PortDecl& port) {
    auto saved = p.lexer_.SavePos();
    if (TryMatchAnsiModportPort(p, port)) return true;
    p.lexer_.RestorePos(saved);
    return false;
  }

  // §25.3.2: an ANSI interface port written with a plain interface name (or
  // any user-named type) as `type_name port_name [dims] [= default]`. The
  // leading identifier is not a known type keyword, so ParseDataType would
  // otherwise return an implicit type and consume the type name as the port
  // name. Returns true and fully parses the port when this two-identifier form
  // is matched; otherwise restores the lexer position and returns false.
  static bool TryParseAnsiNamedTypePort(Parser& p, PortDecl& port) {
    auto saved = p.lexer_.SavePos();
    auto type_tok = p.Consume();
    if (!p.CheckIdentifier()) {
      p.lexer_.RestorePos(saved);
      return false;
    }
    port.data_type.kind = DataTypeKind::kNamed;
    port.data_type.type_name = type_tok.text;
    port.name = p.ExpectIdentifier().text;
    p.ParseUnpackedDims(port.unpacked_dims);
    if (p.Match(TokenKind::kEq)) port.default_value = p.ParseExpr();
    return true;
  }

  // Tries the two no-direction ANSI port forms that begin with a non-keyword
  // identifier: an interface modport port, then a plain named-type port.
  static bool TryParseAnsiModportOrNamedTypePort(Parser& p, PortDecl& port) {
    return TryParseAnsiModportPort(p, port) ||
           TryParseAnsiNamedTypePort(p, port);
  }

  // Parse the data type of an ANSI port, handling the explicit `var`, packed
  // struct/union, `interconnect`, and ordinary data-type forms.
  static void ParseAnsiPortDataType(Parser& p, PortDecl& port) {
    if (p.Match(TokenKind::kKwVar)) {
      port.has_explicit_var = true;
      port.data_type = p.ParseDataType();
      if (port.data_type.kind == DataTypeKind::kImplicit &&
          p.Check(TokenKind::kLBracket)) {
        p.ParsePackedDims(port.data_type);
      }
    } else if (p.Check(TokenKind::kKwStruct) || p.Check(TokenKind::kKwUnion)) {
      port.data_type = p.ParseStructOrUnionType();
      p.ParsePackedDims(port.data_type);
    } else if (p.Match(TokenKind::kKwInterconnect)) {
      port.data_type.kind = DataTypeKind::kWire;
      port.data_type.is_net = true;
      port.data_type.is_interconnect = true;
      if (p.Match(TokenKind::kKwSigned)) {
        port.data_type.is_signed = true;
      } else {
        p.Match(TokenKind::kKwUnsigned);
      }
      p.ParsePackedDims(port.data_type);
    } else {
      port.data_type = p.ParseDataType();
    }
  }

  // Lookahead at the head of a port list: a bare identifier immediately
  // followed by `)`, `,`, or `[` (and not a known type name) indicates the
  // non-ANSI list_of_ports style rather than an ANSI declaration.
  static bool LooksLikeNonAnsiPortList(Parser& p) {
    if (!p.CheckIdentifier()) return false;
    if (p.known_types_.count(p.CurrentToken().text) != 0) return false;
    auto saved = p.lexer_.SavePos();
    p.Consume();
    bool is_non_ansi = p.Check(TokenKind::kRParen) ||
                       p.Check(TokenKind::kComma) ||
                       p.Check(TokenKind::kLBracket);
    p.lexer_.RestorePos(saved);
    return is_non_ansi;
  }

  // After a comma in an ANSI port list, a bare identifier (with no preceding
  // type) continues the previous port's type/direction. Returns true and
  // appends the port when this form is matched; otherwise leaves the lexer
  // untouched and returns false.
  static bool TryParseBareContinuationPort(Parser& p, ModuleDecl& mod,
                                           const PortDecl& prev,
                                           bool is_checker) {
    if (!p.CheckIdentifier() ||
        p.known_types_.count(p.CurrentToken().text) != 0) {
      return false;
    }
    auto saved = p.lexer_.SavePos();
    p.Consume();
    bool looks_bare = p.Check(TokenKind::kLBracket) ||
                      p.Check(TokenKind::kEq) || p.Check(TokenKind::kComma) ||
                      p.Check(TokenKind::kRParen);
    p.lexer_.RestorePos(saved);
    if (!looks_bare) return false;

    PortDecl port;
    port.loc = p.CurrentLoc();
    port.name = p.ExpectIdentifier().text;
    p.ParseUnpackedDims(port.unpacked_dims);
    if (p.Match(TokenKind::kEq)) port.default_value = p.ParseExpr();
    if (!prev.is_explicit_named) {
      port.direction = prev.direction;
      port.data_type = prev.data_type;
    } else {
      ResolvePortDefaults(port, &prev, is_checker);
    }
    mod.ports.push_back(port);
    return true;
  }

  // A type_parameter_declaration in a parameter_port_list. The `type` keyword
  // has already been consumed by the caller.
  static void ParseTypeParamPortDecl(Parser& p, ParamPortList& out,
                                     bool is_localparam_group) {
    // A type_parameter_declaration may carry an optional forward_type keyword
    // (enum, struct, union, class, or interface class) before the identifier
    // to restrict the kinds of type the parameter accepts.
    if (p.Match(TokenKind::kKwInterface)) {
      p.Expect(TokenKind::kKwClass);
    } else if (p.Check(TokenKind::kKwEnum) || p.Check(TokenKind::kKwStruct) ||
               p.Check(TokenKind::kKwUnion) || p.Check(TokenKind::kKwClass)) {
      p.Consume();
    }
    auto name = p.Expect(TokenKind::kIdentifier);
    bool has_default = false;
    if (p.Match(TokenKind::kEq)) {
      has_default = true;
      if (p.Check(TokenKind::kKwType)) {
        p.ParseExpr();
      } else {
        p.ParseDataType();
      }
    }

    if (is_localparam_group && !has_default) {
      p.diag_.Error(name.loc,
                    std::format("localparam type '{}' in parameter port list "
                                "must have a default type",
                                name.text));
    }
    out.params.push_back({name.text, nullptr});
    if (out.param_types) out.param_types->push_back(DataType{});
    out.type_param_names.insert(name.text);
    if (is_localparam_group) out.localparam_port_names.insert(name.text);
    p.known_types_.insert(name.text);
  }

  // A value parameter declaration in a parameter_port_list.
  static void ParseValueParamPortDecl(Parser& p, ParamPortList& out,
                                      bool is_localparam_group) {
    DataType dtype = p.ParseDataType();
    p.ParseImplicitParamRange(dtype);
    auto name = p.Expect(TokenKind::kIdentifier);
    Expr* default_val = nullptr;
    if (p.Match(TokenKind::kEq)) {
      default_val = p.ParseExpr();
    }

    if (is_localparam_group && default_val == nullptr) {
      p.diag_.Error(name.loc,
                    std::format("localparam '{}' in parameter port list must "
                                "have a default value",
                                name.text));
    }
    out.params.push_back({name.text, default_val});
    if (out.param_types) out.param_types->push_back(dtype);
    if (is_localparam_group) out.localparam_port_names.insert(name.text);
  }

  // Parse a leading timeunit/timeprecision declaration and, if the first one
  // was not already paired, its complementary declaration when it follows.
  static void ParseLeadingTimeunitPair(Parser& p, ModuleDecl& mod) {
    bool first_is_unit = p.Check(TokenKind::kKwTimeunit);
    p.ParseTimeunitDecl(&mod);
    bool complement_unit_follows = first_is_unit && !mod.has_timeprecision &&
                                   p.Check(TokenKind::kKwTimeprecision);
    bool complement_precision_follows =
        !first_is_unit && !mod.has_timeunit && p.Check(TokenKind::kKwTimeunit);
    if (complement_unit_follows || complement_precision_follows) {
      p.ParseTimeunitDecl(&mod);
    }
  }

  // §A.1.3: peek past leading attribute_instances; if a port direction follows
  // this is a non-ANSI body port declaration, which is parsed and reported via
  // the true return. Otherwise the lexer position is restored and false is
  // returned so the caller treats it as a generic module item.
  static bool TryParseAttributedNonAnsiPortDecls(Parser& p, ModuleDecl& mod) {
    auto saved = p.lexer_.SavePos();
    p.ParseAttributes();
    if (IsPortDirection(p.CurrentToken().kind)) {
      p.ParseNonAnsiPortDecls(mod);
      return true;
    }
    p.lexer_.RestorePos(saved);
    return false;
  }
};

// §35.5.6: a rich but closed subset of SystemVerilog data types is permitted
// for the formal arguments of DPI import/export subroutines. The clause states
// these are the *only* permitted types: the C-compatible scalar types, the
// scalar 2-/4-state bit types, packed arrays/structs/unions of bit and logic,
// enumerations (interpreted as their base type), and user-defined types
// (typedef/named) built from the above. Anything outside that set -- notably
// event types, virtual interfaces, and net types -- is not a permitted formal
// argument type. Named/typedef forms are accepted here because their underlying
// type is only known after elaboration, and typedef is itself a permitted
// construct per the clause.
static bool IsPermittedDpiFormalType(DataTypeKind kind) {
  switch (kind) {
    case DataTypeKind::kImplicit:
    case DataTypeKind::kLogic:
    case DataTypeKind::kReg:
    case DataTypeKind::kBit:
    case DataTypeKind::kByte:
    case DataTypeKind::kShortint:
    case DataTypeKind::kInt:
    case DataTypeKind::kLongint:
    case DataTypeKind::kInteger:
    case DataTypeKind::kReal:
    case DataTypeKind::kShortreal:
    case DataTypeKind::kRealtime:
    case DataTypeKind::kTime:
    case DataTypeKind::kString:
    case DataTypeKind::kVoid:
    case DataTypeKind::kChandle:
    case DataTypeKind::kNamed:
    case DataTypeKind::kEnum:
    case DataTypeKind::kStruct:
    case DataTypeKind::kUnion:
      return true;
    default:
      return false;
  }
}

// §35.5.5: the result type of an imported function is restricted to "small
// values" -- a tighter set than the §35.5.6 formal-argument types. The
// permitted results are void, the C-compatible scalar integer and real types,
// chandle, string, and *scalar* (single-bit, unpacked) bit/logic. Packed
// bit/logic vectors, the wide 4-state vector types (integer, time), and
// aggregates (struct/union/enum) are not small values and are rejected here.
// Named/typedef results are accepted and deferred to elaboration, since the
// underlying type is not resolved during parsing. The implicit (omitted) kind
// is handled separately, since §35.5.5 also requires the result type to be
// stated explicitly.
static bool IsPermittedDpiResultType(const DataType& type) {
  switch (type.kind) {
    case DataTypeKind::kVoid:
    case DataTypeKind::kByte:
    case DataTypeKind::kShortint:
    case DataTypeKind::kInt:
    case DataTypeKind::kLongint:
    case DataTypeKind::kReal:
    case DataTypeKind::kShortreal:
    case DataTypeKind::kRealtime:
    case DataTypeKind::kChandle:
    case DataTypeKind::kString:
    case DataTypeKind::kNamed:
      return true;
    case DataTypeKind::kBit:
    case DataTypeKind::kLogic:
    case DataTypeKind::kReg:
      // Only the scalar form qualifies; any packed dimension makes it a vector.
      return type.packed_dim_left == nullptr && type.extra_packed_dims.empty();
    default:
      return false;
  }
}

// §35.5.5: validate the (already-parsed) result type of a DPI imported
// function. The type must be stated explicitly and restricted to small values.
static void ValidateDpiResultType(DiagEngine& diag, const ModuleItem* item) {
  if (item->return_type.kind == DataTypeKind::kImplicit) {
    // §35.5.5: an imported function declaration shall explicitly specify a data
    // type or void for its result. Unlike a native function declaration, an
    // omitted (implicit) return type is not allowed.
    diag.Error(item->loc,
               "an imported function must explicitly specify a data type or "
               "void for its result");
  } else if (!IsPermittedDpiResultType(item->return_type)) {
    // §35.5.5: function results are restricted to small values; the type is
    // outside the permitted set.
    diag.Error(item->loc,
               "result type is not permitted for a DPI imported function; "
               "function results are restricted to small values");
  }
}

// §35.5.4: the ref qualifier is forbidden on the formal arguments of a DPI
// import declaration.
static void ValidateDpiImportNoRefArgs(DiagEngine& diag,
                                       const ModuleItem* item) {
  for (const auto& arg : item->func_args) {
    if (arg.direction == Direction::kRef) {
      diag.Error(item->loc,
                 "ref qualifier cannot be used in a DPI import declaration");
      break;
    }
  }
}

// §35.5.6: the listed types are the only permitted types for formal arguments
// of imported subroutines; a union argument must additionally be packed.
static void ValidateDpiImportFormalTypes(DiagEngine& diag,
                                         const ModuleItem* item) {
  for (const auto& arg : item->func_args) {
    if (!IsPermittedDpiFormalType(arg.data_type.kind)) {
      diag.Error(item->loc,
                 std::format("type of formal argument '{}' is not permitted "
                             "for a DPI imported subroutine",
                             arg.name));
    } else if (arg.data_type.kind == DataTypeKind::kUnion &&
               !arg.data_type.is_packed) {
      // §35.5.6: among the type-constructing forms in the permitted set, a
      // union is allowed in its packed form only. An unpacked union is
      // therefore not a permitted formal-argument type.
      diag.Error(item->loc,
                 std::format("unpacked union formal argument '{}' is not "
                             "permitted for a DPI imported subroutine; only "
                             "the packed form of a union is allowed",
                             arg.name));
    }
  }
}

static Direction TokenToDirection(TokenKind kind) {
  switch (kind) {
    case TokenKind::kKwInput:
      return Direction::kInput;
    case TokenKind::kKwOutput:
      return Direction::kOutput;
    case TokenKind::kKwInout:
      return Direction::kInout;
    case TokenKind::kKwRef:
      return Direction::kRef;
    default:
      return Direction::kNone;
  }
}

ModuleItem* Parser::ParseImportItem() {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kImportDecl;
  item->loc = CurrentLoc();

  if (CurrentToken().kind == TokenKind::kSystemIdentifier &&
      CurrentToken().text == "$unit") {
    diag_.Error(CurrentLoc(),
                "the compilation-unit scope cannot be used with an "
                "import declaration");
    Consume();
    if (Check(TokenKind::kColonColon)) Consume();
    if (Check(TokenKind::kStar)) {
      Consume();
      item->import_item.is_wildcard = true;
    } else if (Check(TokenKind::kIdentifier)) {
      item->import_item.item_name = Consume().text;
    }
    return item;
  }
  item->import_item.package_name = Expect(TokenKind::kIdentifier).text;
  Expect(TokenKind::kColonColon);
  if (Match(TokenKind::kStar)) {
    item->import_item.is_wildcard = true;
  } else {
    item->import_item.item_name = Expect(TokenKind::kIdentifier).text;
  }
  return item;
}

void Parser::ParseImportDecl(std::vector<ModuleItem*>& items) {
  Expect(TokenKind::kKwImport);

  if (Check(TokenKind::kStringLiteral)) {
    items.push_back(ParseDpiImport());
    return;
  }
  items.push_back(ParseImportItem());
  while (Match(TokenKind::kComma)) {
    items.push_back(ParseImportItem());
  }
  Expect(TokenKind::kSemicolon);
}

void Parser::ParseExportDecl(std::vector<ModuleItem*>& items) {
  auto loc = CurrentLoc();
  Expect(TokenKind::kKwExport);

  if (Check(TokenKind::kStringLiteral)) {
    items.push_back(ParseDpiExport(loc));
    return;
  }
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kExportDecl;
  item->loc = loc;
  if (Match(TokenKind::kStar)) {
    item->import_item.package_name = "*";
    Expect(TokenKind::kColonColon);
    Expect(TokenKind::kStar);
    item->import_item.is_wildcard = true;
  } else {
    item->import_item.package_name = Expect(TokenKind::kIdentifier).text;
    Expect(TokenKind::kColonColon);
    if (Match(TokenKind::kStar)) {
      item->import_item.is_wildcard = true;
    } else {
      item->import_item.item_name = Expect(TokenKind::kIdentifier).text;
    }
  }
  items.push_back(item);

  while (Match(TokenKind::kComma)) {
    auto* next = arena_.Create<ModuleItem>();
    next->kind = ModuleItemKind::kExportDecl;
    next->loc = loc;
    next->import_item.package_name = Expect(TokenKind::kIdentifier).text;
    Expect(TokenKind::kColonColon);
    if (Match(TokenKind::kStar)) {
      next->import_item.is_wildcard = true;
    } else {
      next->import_item.item_name = Expect(TokenKind::kIdentifier).text;
    }
    items.push_back(next);
  }
  Expect(TokenKind::kSemicolon);
}

ModuleItem* Parser::ParseDpiImport() {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kDpiImport;
  item->loc = CurrentLoc();
  ParserPortHelpers::ParseDpiSpecString(*this, item);

  if (Match(TokenKind::kKwPure)) {
    item->dpi_is_pure = true;
  }
  if (Match(TokenKind::kKwContext)) {
    item->dpi_is_context = true;
  }

  ParserPortHelpers::TryParseDpiCName(*this, item);

  if (Match(TokenKind::kKwTask)) {
    item->dpi_is_task = true;
  } else {
    Expect(TokenKind::kKwFunction);
  }

  // §35.5.1.3: the pure property is reserved for imported functions; an
  // imported task can never be declared pure.
  if (item->dpi_is_task && item->dpi_is_pure) {
    diag_.Error(item->loc, "an imported task cannot be declared pure");
  }

  if (!item->dpi_is_task) {
    item->return_type = ParseDataType();
    ValidateDpiResultType(diag_, item);
  }
  item->name = Expect(TokenKind::kIdentifier).text;

  if (Check(TokenKind::kLParen)) {
    item->func_args = ParseFunctionArgs(false);
  }
  ValidateDpiImportNoRefArgs(diag_, item);
  ValidateDpiImportFormalTypes(diag_, item);
  Expect(TokenKind::kSemicolon);
  return item;
}

ModuleItem* Parser::ParseDpiExport(SourceLoc loc) {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kDpiExport;
  item->loc = loc;
  ParserPortHelpers::ParseDpiSpecString(*this, item);

  ParserPortHelpers::TryParseDpiCName(*this, item);

  if (Match(TokenKind::kKwTask)) {
    item->dpi_is_task = true;
  } else {
    Expect(TokenKind::kKwFunction);
  }
  item->name = Expect(TokenKind::kIdentifier).text;
  Expect(TokenKind::kSemicolon);
  return item;
}

void Parser::ParseParamPortDecl(
    std::vector<std::pair<std::string_view, Expr*>>& params,
    std::unordered_set<std::string_view>& type_param_names,
    std::unordered_set<std::string_view>& localparam_port_names,
    bool& is_localparam_group, std::vector<DataType>* param_types) {
  if (Match(TokenKind::kKwLocalparam)) {
    is_localparam_group = true;
  } else if (Match(TokenKind::kKwParameter)) {
    is_localparam_group = false;
  }

  ParamPortList out{params, type_param_names, localparam_port_names,
                    param_types};
  if (Match(TokenKind::kKwType)) {
    ParserPortHelpers::ParseTypeParamPortDecl(*this, out, is_localparam_group);
    return;
  }
  ParserPortHelpers::ParseValueParamPortDecl(*this, out, is_localparam_group);
}

void Parser::ParseParamsPortsAndSemicolon(ModuleDecl& decl) {
  SourceLoc import_loc;
  bool has_header_import = false;
  while (Check(TokenKind::kKwImport)) {
    if (!has_header_import) import_loc = CurrentLoc();
    has_header_import = true;
    size_t before = decl.items.size();
    ParseImportDecl(decl.items);
    for (size_t i = before; i < decl.items.size(); ++i) {
      decl.items[i]->import_item.is_header = true;
    }
  }
  if (has_header_import && !Check(TokenKind::kHash) &&
      !Check(TokenKind::kLParen)) {
    diag_.Error(import_loc,
                "package_import_declaration in ansi header must be followed "
                "by parameter_port_list or list_of_port_declarations");
  }
  if (Check(TokenKind::kHash)) {
    Consume();
    Expect(TokenKind::kLParen);
    decl.has_param_port_list = true;
    if (!Check(TokenKind::kRParen)) {
      bool is_lp_group = false;
      ParseParamPortDecl(decl.params, decl.type_param_names,
                         decl.localparam_port_names, is_lp_group,
                         &decl.param_types);
      while (Match(TokenKind::kComma)) {
        ParseParamPortDecl(decl.params, decl.type_param_names,
                           decl.localparam_port_names, is_lp_group,
                           &decl.param_types);
      }
    }
    Expect(TokenKind::kRParen);
  }
  if (Check(TokenKind::kLParen)) {
    ParsePortList(decl);
  }
  Expect(TokenKind::kSemicolon);
}

// A port with an inferred (non-var, non-net) type becomes an implicit net when
// its direction allows it: inputs/inouts always, outputs only when the type was
// left implicit.
static void InferImplicitNetForPort(PortDecl& port) {
  if (port.has_explicit_var || port.data_type.is_net) return;
  switch (port.direction) {
    case Direction::kInput:
    case Direction::kInout:
      port.data_type.is_net = true;
      break;
    case Direction::kOutput:
      if (port.data_type.kind == DataTypeKind::kImplicit)
        port.data_type.is_net = true;
      break;
    default:
      break;
  }
}

static void ResolvePortDefaults(PortDecl& port, const PortDecl* prev,
                                bool is_checker) {
  if (port.is_interface_port) return;
  if (port.data_type.kind == DataTypeKind::kNamed &&
      !port.data_type.modport_name.empty())
    return;

  if (port.is_explicit_named) {
    if (prev && port.direction == Direction::kNone)
      port.direction = prev->direction;
    return;
  }

  // §17.2: when a checker formal argument omits its direction, the direction
  // of the previous formal is inferred; the first formal defaults to input.
  // Module-style ports instead default to inout when no prior direction exists.
  if (port.direction == Direction::kNone)
    port.direction = prev
                         ? prev->direction
                         : (is_checker ? Direction::kInput : Direction::kInout);

  InferImplicitNetForPort(port);

  if (port.data_type.kind == DataTypeKind::kImplicit)
    port.data_type.kind = DataTypeKind::kLogic;
}

void Parser::ParsePortList(ModuleDecl& mod) {
  Expect(TokenKind::kLParen);
  if (Check(TokenKind::kRParen)) {
    Consume();
    return;
  }

  if (Check(TokenKind::kDotStar)) {
    Consume();
    mod.has_wildcard_ports = true;
    Expect(TokenKind::kRParen);
    return;
  }

  if (Check(TokenKind::kDot) || Check(TokenKind::kLBrace)) {
    ParseNonAnsiPortList(mod);
    return;
  }

  if (ParserPortHelpers::LooksLikeNonAnsiPortList(*this)) {
    ParseNonAnsiPortList(mod);
    return;
  }

  const bool kIsChecker = mod.decl_kind == ModuleDeclKind::kChecker;
  mod.ports.push_back(ParsePortDecl());
  ResolvePortDefaults(mod.ports.back(), nullptr, kIsChecker);
  while (Match(TokenKind::kComma)) {
    PortDecl prev = mod.ports.back();

    if (ParserPortHelpers::TryParseBareContinuationPort(*this, mod, prev,
                                                        kIsChecker)) {
      continue;
    }
    mod.ports.push_back(ParsePortDecl());
    ResolvePortDefaults(mod.ports.back(), &prev, kIsChecker);
  }
  Expect(TokenKind::kRParen);
}

void Parser::ParseNonAnsiPortList(ModuleDecl& mod) {
  mod.is_non_ansi_ports = true;

  do {
    if (Check(TokenKind::kComma) || Check(TokenKind::kRParen)) {
      PortDecl port;
      port.loc = CurrentLoc();
      mod.ports.push_back(port);
      continue;
    }
    mod.ports.push_back(ParserPortHelpers::ParseNonAnsiPortEntry(*this));
  } while (Match(TokenKind::kComma));
  Expect(TokenKind::kRParen);
}

PortDecl Parser::ParsePortDecl() {
  PortDecl port;

  // §A.1.3: each ansi_port_declaration in a list_of_port_declarations may be
  // preceded by attribute_instances. They carry no ANSI port semantics here,
  // so consume and discard them before the port itself.
  ParseAttributes();

  port.loc = CurrentLoc();

  Direction dir = TokenToDirection(CurrentToken().kind);
  if (dir != Direction::kNone) {
    port.direction = dir;
    Consume();
  }

  if (Check(TokenKind::kDot)) {
    port.is_explicit_named = true;
    Consume();
    port.name = ExpectIdentifier().text;
    Expect(TokenKind::kLParen);
    if (!Check(TokenKind::kRParen)) {
      port.port_expr = ParseExpr();
    }
    Expect(TokenKind::kRParen);
    return port;
  }

  if (Check(TokenKind::kKwInterface)) {
    ParserPortHelpers::ParseAnsiInterfacePort(*this, port);
    return port;
  }

  if (dir == Direction::kNone && CheckIdentifier() &&
      known_types_.count(CurrentToken().text) == 0) {
    if (ParserPortHelpers::TryParseAnsiModportOrNamedTypePort(*this, port)) {
      return port;
    }
  }

  ParserPortHelpers::ParseAnsiPortDataType(*this, port);

  if (port.data_type.kind == DataTypeKind::kNamed && Check(TokenKind::kDot)) {
    Consume();
    port.data_type.modport_name = ExpectIdentifier().text;
  }

  if (port.data_type.kind == DataTypeKind::kImplicit &&
      !port.data_type.packed_dim_left && Check(TokenKind::kLBracket)) {
    Consume();
    port.data_type.packed_dim_left = ParseExpr();
    Expect(TokenKind::kColon);
    port.data_type.packed_dim_right = ParseExpr();
    Expect(TokenKind::kRBracket);
  }

  auto name_tok = ExpectIdentifier();
  port.name = name_tok.text;

  ParseUnpackedDims(port.unpacked_dims);

  if (Match(TokenKind::kEq)) {
    port.default_value = ParseExpr();
  }
  return port;
}

static bool HasNonAnsiPorts(const ModuleDecl& mod) {
  if (mod.ports.empty()) return false;
  auto& first = mod.ports[0];
  if (first.direction != Direction::kNone) return false;

  if (first.is_interface_port) return false;
  if (first.data_type.kind != DataTypeKind::kImplicit) return false;
  return true;
}

void Parser::ParseModuleBody(ModuleDecl& mod) {
  auto* prev_module = current_module_;
  current_module_ = &mod;
  bool non_ansi = HasNonAnsiPorts(mod);

  if (Check(TokenKind::kKwTimeunit) || Check(TokenKind::kKwTimeprecision)) {
    ParserPortHelpers::ParseLeadingTimeunitPair(*this, mod);
  }
  while (!Check(TokenKind::kKwEndmodule) && !AtEnd()) {
    if (Match(TokenKind::kSemicolon)) continue;
    if (non_ansi && IsPortDirection(CurrentToken().kind)) {
      ParseNonAnsiPortDecls(mod);
      continue;
    }
    // §A.1.3: a non-ANSI body port_declaration may carry leading
    // attribute_instances. Peek past them; if a port direction follows, this is
    // a port declaration rather than a generic module item.
    if (non_ansi && Check(TokenKind::kAttrStart) &&
        ParserPortHelpers::TryParseAttributedNonAnsiPortDecls(*this, mod)) {
      continue;
    }
    ParseModuleItem(mod.items);
  }
  current_module_ = prev_module;
}

void Parser::ParseNonAnsiPortDecls(ModuleDecl& mod) {
  Direction dir = Direction::kNone;
  auto tk = CurrentToken().kind;
  if (tk == TokenKind::kKwInput) dir = Direction::kInput;
  if (tk == TokenKind::kKwOutput) dir = Direction::kOutput;
  if (tk == TokenKind::kKwInout) dir = Direction::kInout;
  if (tk == TokenKind::kKwRef) dir = Direction::kRef;
  Consume();

  // §23.2.2.2 / §25.3.3: a generic interface reference uses the `interface`
  // keyword as a placeholder port type. Such a port may only be declared with
  // the ANSI list_of_port_declarations style; encountering it inside a non-ANSI
  // body port declaration means it was written with the non-ANSI list_of_ports
  // style, which is illegal.
  if (Check(TokenKind::kKwInterface)) {
    diag_.Error(CurrentLoc(),
                "generic interface port must be declared with ANSI-style port "
                "declarations, not the non-ANSI port style");
    while (!Check(TokenKind::kSemicolon) && !Check(TokenKind::kKwEndmodule) &&
           !AtEnd())
      Consume();
    Match(TokenKind::kSemicolon);
    return;
  }

  auto dtype = ParseDataType();

  if (dtype.kind == DataTypeKind::kImplicit && Check(TokenKind::kLBracket)) {
    Consume();
    dtype.packed_dim_left = ParseExpr();
    Expect(TokenKind::kColon);
    dtype.packed_dim_right = ParseExpr();
    Expect(TokenKind::kRBracket);
  }

  do {
    ParserPortHelpers::ApplyNonAnsiPortDecl(*this, mod, dir, dtype);
  } while (Match(TokenKind::kComma));
  Expect(TokenKind::kSemicolon);
}

}  // namespace delta
