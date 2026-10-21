#include <cstddef>
#include <format>
#include <string_view>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "common/types.h"
#include "lexer/token.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"
#include "parser/param_port_list.h"
#include "parser/parser.h"
#include "parser/parser_dpi_validate.h"
#include "parser/parser_headers.h"
#include "parser/parser_token_skips.h"

namespace delta {

static void ResolvePortDefaults(PortDecl& port, const PortDecl* prev,
                                bool is_checker);

// The pieces of port parsing that more than one of Parser's port entry points
// needs, gathered so that neither the ANSI nor the non-ANSI path repeats them.
struct ParserPortHelpers {
  // Apply one non-ANSI body port declaration (a single name + dims) to the
  // matching already-declared port(s), reporting a duplicate-direction error.
  // `shape` holds what the declaration gives every name it declares: its
  // direction, its data type, whether it was written with `var`, and the
  // attributes written before it.
  static void ApplyNonAnsiPortDecl(Parser& p, ModuleDecl& mod,
                                   const PortDecl& shape) {
    auto loc = p.CurrentLoc();
    auto name = p.Expect(TokenKind::kIdentifier, Subclause("23.2.2.1")).text;
    std::vector<Expr*> dims;
    p.ParseUnpackedDims(dims);
    bool found = false;
    for (auto& port : mod.ports) {
      if (port.name != name) continue;

      if (!found && port.direction != Direction::kNone) {
        p.diag_.Error(loc,
                      std::format("duplicate port declaration for '{}'", name),
                      Subclause("23.2.2.1"));
      }
      found = true;
      port.direction = shape.direction;
      port.data_type = shape.data_type;
      port.has_explicit_var = shape.has_explicit_var;
      port.attrs = shape.attrs;
      port.unpacked_dims = dims;
    }
    // §23.5: with a `.*` module header the port names come from the module's
    // extern declaration, which is not visible until elaboration, so the port
    // is materialized from this body declaration; elaboration keeps these
    // body-declared ports instead of the (name-only) extern ports.
    if (found) return;
    PortDecl np = shape;
    np.name = name;
    np.unpacked_dims = dims;
    np.loc = loc;
    // §23.2.2.1 (printed page 733), Example 5: in `renamed_concat(.a({b, c}),
    // f, .g(h[1]))` the body's `input b, c;` and `output [1:0] h;` declare the
    // objects ports a and g stand for; the elaborator declares them from these
    // and gives an explicitly named port the direction of what it names.
    if (mod.has_wildcard_ports) {
      mod.ports.push_back(np);
    } else {
      mod.port_expr_objects.push_back(np);
    }
  }

  // A non-ANSI list_of_ports bit-/part-select on a bare port name, held as a
  // select port_expr. §23.2.2.1 writes the name first, so both begin at it.
  static Expr* ParseNonAnsiPortSelect(Parser& p, const Token& name_tok) {
    auto* ref = p.arena_.Create<Expr>();
    ref->kind = ExprKind::kIdentifier;
    ref->text = name_tok.text;
    ref->range.start = name_tok.loc;
    p.Consume();
    auto* idx = p.ParseExpr();
    auto* sel = p.arena_.Create<Expr>();
    sel->kind = ExprKind::kSelect;
    sel->range.start = ref->range.start;
    sel->base = ref;
    sel->index = idx;
    // A.1.3: the constant_part_select_range of a port_reference is a range or
    // an indexed range, the latter's width held in index_end as §11.5.1's is.
    if (p.Match(TokenKind::kPlusColon)) {
      sel->is_part_select_plus = true;
      sel->index_end = p.ParseExpr();
    } else if (p.Match(TokenKind::kMinusColon)) {
      sel->is_part_select_minus = true;
      sel->index_end = p.ParseExpr();
    } else if (p.Match(TokenKind::kColon)) {
      sel->index_end = p.ParseExpr();
    }
    p.Expect(TokenKind::kRBracket, Subclause("23.2.2.1"));
    return sel;
  }

  // §10.9: an assignment pattern expression shall not be written in a port
  // expression of a module, interface or program declaration, the
  // port_expression of a non-ANSI list of ports. A port expression is built of
  // names, their constant selects and a concatenation of these, so a pattern
  // is reported wherever in the expression it stands, a typed pattern's being
  // the operand of its cast.
  static void RejectPatternInPortExpr(Parser& p, const Expr* e) {
    if (e->kind == ExprKind::kAssignmentPattern) {
      p.diag_.Error(e->range.start,
                    "an assignment pattern cannot be written in a port "
                    "expression",
                    Subclause("10.9"));
      return;
    }
    if (e->lhs != nullptr) RejectPatternInPortExpr(p, e->lhs);
    for (const Expr* item : e->elements) RejectPatternInPortExpr(p, item);
  }

  static Expr* ParsePortExpression(Parser& p) {
    Expr* e = p.ParseExpr();
    RejectPatternInPortExpr(p, e);
    return e;
  }

  // Parse a single non-ANSI list_of_ports entry (.name(expr), {concat}, or a
  // bare name with an optional bit-/part-select).
  static PortDecl ParseNonAnsiPortEntry(Parser& p) {
    PortDecl port;
    port.loc = p.CurrentLoc();
    if (p.Match(TokenKind::kDot)) {
      port.is_explicit_named = true;
      port.name = p.ExpectIdentifier(Subclause("23.2.2.1")).text;
      p.Expect(TokenKind::kLParen, Subclause("23.2.2.1"));
      if (!p.Check(TokenKind::kRParen)) {
        port.port_expr = ParsePortExpression(p);
      }
      p.Expect(TokenKind::kRParen, Subclause("23.2.2.1"));
    } else if (p.Check(TokenKind::kLBrace)) {
      port.port_expr = ParsePortExpression(p);
    } else {
      Token name_tok = p.ExpectIdentifier(Subclause("23.2.2.1"));
      port.name = name_tok.text;
      if (p.Check(TokenKind::kLBracket)) {
        port.port_expr = ParseNonAnsiPortSelect(p, name_tok);
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
      port.data_type.modport_name =
          p.ExpectIdentifier(Subclause("25.3.3")).text;
    }
    port.name = p.ExpectIdentifier(Subclause("25.3.3")).text;
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
    port.name = p.ExpectIdentifier(Subclause("25.5")).text;
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

  // Parse the simple interface-port form `iface_type port_name` (25.3.2): no
  // direction, an unknown (non-data) type name, and not a modport form. Returns
  // true and fully parses the port when matched; otherwise restores the lexer
  // position and returns false so the caller parses an ordinary data type.
  static bool TryParseSimpleInterfacePort(Parser& p, PortDecl& port) {
    auto saved = p.lexer_.SavePos();
    auto type_tok = p.Consume();
    if (!p.CheckIdentifier()) {
      p.lexer_.RestorePos(saved);
      return false;
    }
    port.data_type.kind = DataTypeKind::kNamed;
    port.data_type.type_name = type_tok.text;
    port.is_interface_port = true;
    port.name = p.ExpectIdentifier(Subclause("25.3.2")).text;
    p.ParseUnpackedDims(port.unpacked_dims);
    if (p.Match(TokenKind::kEq)) {
      port.default_value = p.ParseExpr();
    }
    return true;
  }

  // Parses a `.name(port_expr)` explicit-named ANSI port. Returns true and
  // fills `port` when the current token begins such a port; false otherwise.
  static bool TryParseExplicitNamedPort(Parser& p, PortDecl& port) {
    if (!p.Check(TokenKind::kDot)) return false;
    port.is_explicit_named = true;
    p.Consume();
    port.name = p.ExpectIdentifier(Subclause("23.2.2.2")).text;
    p.Expect(TokenKind::kLParen, Subclause("23.2.2.2"));
    // §23.2.2.2 lets this form bind an assignment pattern expression of
    // elements declared in the module: Syntax 23-4 gives it an expression,
    // not the port_expression §10.9 keeps patterns out of.
    if (!p.Check(TokenKind::kRParen)) {
      port.port_expr = p.ParseExpr();
    }
    p.Expect(TokenKind::kRParen, Subclause("23.2.2.2"));
    return true;
  }

  // Parses the data type written for a port, whatever port kind was written in
  // front of it. Syntax 23-4 spells both port kinds against the same
  // data_type_or_implicit -- `net_port_type ::= [ net_type ]
  // data_type_or_implicit` and `var_data_type ::= data_type | var
  // data_type_or_implicit` -- so the type after `var` is the type that stands
  // there without it. A struct or union defined in place and an enumeration
  // defined in place are both data_type forms, and both are parsed here for the
  // same reason: the general data-type parse recognizes only a type that is
  // already named, and leaves the keyword unconsumed for the port name to be
  // read from.
  static DataType ParsePortDataTypeBody(Parser& p) {
    if (p.Check(TokenKind::kKwStruct) || p.Check(TokenKind::kKwUnion)) {
      auto dtype = p.ParseStructOrUnionType();
      p.ParsePackedDims(dtype);
      return dtype;
    }
    if (p.Check(TokenKind::kKwEnum)) return p.ParseEnumType();
    // §23.2.2.2's port type is A.2.2.1's data_type, a type_identifier behind
    // a package_scope among its forms (§26.3), so `input A::instruction_t a`
    // reads the scoped type rather than taking `A` for the port's name.
    return p.ParseDeclaredDataType();
  }

  // Syntax 23-4 writes the third net_port_type form as `interconnect
  // implicit_data_type`, so what follows the keyword is a signing and packed
  // dimensions and never a data type.
  static void ParseInterconnectPortType(Parser& p, PortDecl& port) {
    port.data_type.kind = DataTypeKind::kWire;
    port.data_type.is_net = true;
    port.data_type.is_interconnect = true;
    if (p.Match(TokenKind::kKwSigned)) {
      port.data_type.is_signed = true;
    } else {
      p.Match(TokenKind::kKwUnsigned);
    }
    p.ParsePackedDims(port.data_type);
  }

  // Parse the data type of an ANSI port, handling the explicit `var`,
  // `interconnect`, and plain forms. §23.2.2.3 counts `var` among the port
  // kinds -- a port kind there being either a net type keyword or `var` -- so
  // it says what the port is rather than what type it has, and the type written
  // after it is parsed the same way as one written with no port kind at all.
  static void ParseAnsiPortDataType(Parser& p, PortDecl& port) {
    if (p.Match(TokenKind::kKwVar)) {
      port.has_explicit_var = true;
      port.data_type = ParsePortDataTypeBody(p);
      if (port.data_type.kind == DataTypeKind::kImplicit &&
          p.Check(TokenKind::kLBracket)) {
        p.ParsePackedDims(port.data_type);
      }
      return;
    }
    if (p.Match(TokenKind::kKwInterconnect)) {
      ParseInterconnectPortType(p, port);
      return;
    }
    port.data_type = ParsePortDataTypeBody(p);
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

  // §6.18 / §23.2.2.1: an ANSI port type may be a user-defined type declared
  // later in the same module body (a forward type reference), so it is not yet
  // in known_types_ when the port list is parsed. With an explicit direction an
  // interface port is impossible, so two consecutive identifiers (`input pair_t
  // p`) unambiguously name a type followed by the port name; report that so the
  // first identifier is parsed as a named type rather than the port name.
  static bool LooksLikeForwardNamedType(Parser& p, Direction dir) {
    if (dir == Direction::kNone || !p.CheckIdentifier()) return false;
    if (p.known_types_.count(p.CurrentToken().text) != 0) return false;
    auto saved = p.lexer_.SavePos();
    p.Consume();
    bool type_then_name = p.CheckIdentifier();
    p.lexer_.RestorePos(saved);
    return type_then_name;
  }

  // Parses the data type of an ANSI port, treating a forward-referenced
  // user-defined type (a two-identifier `type name` head) as a named type and
  // otherwise deferring to the general port data-type parse.
  static void ParsePortType(Parser& p, PortDecl& port, Direction dir) {
    if (LooksLikeForwardNamedType(p, dir)) {
      port.data_type = p.ParseNamedType();
    } else {
      ParseAnsiPortDataType(p, port);
    }
  }

  // The three keyword forms of A.1.8's property_formal_type, `sequence`,
  // `untyped` and `property`, which a checker_port_item may carry where a
  // module's port carries a data type. Consumes the keyword and records it
  // when the port opens with one; otherwise leaves the lexer untouched and
  // returns false so the caller parses a data type.
  static bool TryParseKeywordFormalType(Parser& p, PortDecl& port) {
    switch (p.CurrentToken().kind) {
      case TokenKind::kKwSequence:
        port.formal_type = PropertyFormalType::kSequence;
        break;
      case TokenKind::kKwUntyped:
        port.formal_type = PropertyFormalType::kUntyped;
        break;
      case TokenKind::kKwProperty:
        port.formal_type = PropertyFormalType::kProperty;
        break;
      default:
        return false;
    }
    p.Consume();
    return true;
  }

  // The data type of an ANSI port and what may trail it: a modport after a
  // named type, or one packed dimension after an implicit type.
  static void ParseTypedPortHead(Parser& p, PortDecl& port, Direction dir) {
    ParsePortType(p, port, dir);

    if (port.data_type.kind == DataTypeKind::kNamed &&
        p.Check(TokenKind::kDot)) {
      p.Consume();
      port.data_type.modport_name = p.ExpectIdentifier(Subclause("25.5")).text;
    }

    if (port.data_type.kind == DataTypeKind::kImplicit &&
        !port.data_type.packed_dim_left && p.Check(TokenKind::kLBracket)) {
      p.Consume();
      port.data_type.packed_dim_left = p.ParseExpr();
      p.Expect(TokenKind::kColon, Subclause("23.2.2.3"));
      port.data_type.packed_dim_right = p.ParseExpr();
      p.Expect(TokenKind::kRBracket, Subclause("23.2.2.3"));
    }
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
    port.name = p.ExpectIdentifier(Subclause("23.2.2.2")).text;
    p.ParseUnpackedDims(port.unpacked_dims);
    if (p.Match(TokenKind::kEq)) port.default_value = p.ParseExpr();
    if (!prev.is_explicit_named) {
      port.direction = prev.direction;
      port.data_type = prev.data_type;
      port.formal_type = prev.formal_type;
    } else {
      ResolvePortDefaults(port, &prev, is_checker);
    }
    mod.ports.push_back(port);
    return true;
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
  // §25.3.3: a generic interface reference is a port type of the ANSI
  // list_of_port_declarations alone. In a module whose header is a non-ANSI
  // list_of_ports, `interface a;` or `interface.mp a;` naming one of those
  // ports is that reference written in the style the clause forbids, though it
  // begins as a nested interface declaration would. Reports it and reads it to
  // its `;`; where the name is no port of the header, the text is left to the
  // module item it begins.
  static bool TryParseNonAnsiGenericInterfacePort(Parser& p, ModuleDecl& mod) {
    auto saved = p.lexer_.SavePos();
    SourceLoc loc = p.CurrentLoc();
    p.Consume();
    if (p.Match(TokenKind::kDot) && p.CheckIdentifier()) p.Consume();
    bool names_port = false;
    if (p.CheckIdentifier()) {
      for (const auto& port : mod.ports)
        names_port |= port.name == p.CurrentToken().text;
    }
    if (!names_port) {
      p.lexer_.RestorePos(saved);
      return false;
    }
    p.diag_.Error(loc,
                  "generic interface port must be declared with ANSI-style "
                  "port declarations, not the non-ANSI port style",
                  Subclause("25.3.3"));
    while (!p.Check(TokenKind::kSemicolon) &&
           !p.Check(TokenKind::kKwEndmodule) && !p.AtEnd())
      p.Consume();
    p.Match(TokenKind::kSemicolon);
    return true;
  }

  static bool TryParseAttributedNonAnsiPortDecls(Parser& p, ModuleDecl& mod) {
    auto saved = p.lexer_.SavePos();
    std::vector<Attribute> attrs = p.ParseAttributes();
    if (IsPortDirection(p.CurrentToken().kind)) {
      p.ParseNonAnsiPortDecls(mod, std::move(attrs));
      return true;
    }
    p.lexer_.RestorePos(saved);
    return false;
  }

  // A port declaration a non-ANSI module's body holds at the current token, or
  // false where the token begins some other module item: one with a direction,
  // one behind attribute_instances (A.1.3), or the generic interface reference
  // §25.3.3 forbids in that style.
  static bool TryParseNonAnsiBodyPortDecl(Parser& p, ModuleDecl& mod) {
    if (IsPortDirection(p.CurrentToken().kind)) {
      p.ParseNonAnsiPortDecls(mod);
      return true;
    }
    if (p.Check(TokenKind::kAttrStart))
      return TryParseAttributedNonAnsiPortDecls(p, mod);
    if (p.Check(TokenKind::kKwInterface))
      return TryParseNonAnsiGenericInterfacePort(p, mod);
    return false;
  }
};

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

// The subclause whose syntax footnote requires a list after an ansi header's
// package import, for the kind of design element the header opens.
static const char* HeaderImportSubclause(ModuleDeclKind kind) {
  switch (kind) {
    case ModuleDeclKind::kProgram:
      return "24.3";
    case ModuleDeclKind::kInterface:
      return "25.3";
    default:
      return "23.2.1";
  }
}

void Parser::ParseParamsPortsAndSemicolon(ModuleDecl& decl) {
  const size_t kFirstSite = time_literals_.size();
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
  // The footnote is the module header's in §23.2.1, the program header's in
  // §24.3 (Syntax 24-1 footnote 1) and the interface header's in §25.3
  // (Syntax 25-1 footnote 1).
  if (has_header_import && !Check(TokenKind::kHash) &&
      !Check(TokenKind::kLParen)) {
    diag_.Error(import_loc,
                "package_import_declaration in ansi header must be followed "
                "by parameter_port_list or list_of_port_declarations",
                Subclause(HeaderImportSubclause(decl.decl_kind)));
  }
  HeaderPartLocs parts;
  if (has_header_import) parts.import_loc = import_loc;
  if (Check(TokenKind::kHash)) {
    parts.params_loc = CurrentLoc();
    Consume();
    Expect(TokenKind::kLParen, Subclause("23.2.3"));
    decl.has_param_port_list = true;
    ParamPortList out{decl.params,
                      decl.type_param_names,
                      decl.localparam_port_names,
                      &decl.param_types,
                      &decl.param_port_unpacked_dims,
                      &decl.param_port_locs};
    ParseParamPortDecls(out);
    Expect(TokenKind::kRParen, Subclause("23.2.3"));
  }
  if (Check(TokenKind::kLParen)) {
    parts.ports_loc = CurrentLoc();
    ParsePortList(decl);
  }
  ReportUnwrittenHeaderParts(decl, parts, diag_);
  Expect(TokenKind::kSemicolon, Subclause("23.2.1"));
  // §3.14.2.3: a time literal in the header -- a parameter's or a port's
  // default -- belongs to the element's time scope, which current_module_
  // names only once the body begins.
  for (size_t i = kFirstSite; i < time_literals_.size(); ++i) {
    time_literals_[i] =
        TimeLiteralSite{time_literals_[i].literal, &decl, nullptr};
  }
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

// Whether a checker formal was written with no type at all: A.1.8's
// property_formal_type reaches data_type_or_implicit, and an implicit type
// with a signing or a packed dimension is still a type written.
static bool FormalTypeOmitted(const PortDecl& port) {
  return port.formal_type == PropertyFormalType::kData &&
         port.data_type.kind == DataTypeKind::kImplicit &&
         !port.data_type.is_signed && !port.data_type.packed_dim_left;
}

// The keyword a formal's property_formal_type was written with.
static const char* FormalTypeKeyword(PropertyFormalType type) {
  switch (type) {
    case PropertyFormalType::kSequence:
      return "sequence";
    case PropertyFormalType::kUntyped:
      return "untyped";
    case PropertyFormalType::kProperty:
      return "property";
    default:
      return "";
  }
}

// §17.2's two rules on the type of a checker formal: a formal written with a
// direction must also be written with a type, and an output formal may not be
// typed untyped, sequence or property. `type_omitted` and `direction_written`
// record the port as it was written, before ResolvePortDefaults gave it the
// direction and type it inherits, since inheriting is what an omitted type and
// direction do. A formal that omits its type with a direction written breaks
// the first rule whichever direction it is, so an output written `output a` is
// reported once, under that rule; the second is left the output written with
// one of the three keywords, or inheriting one.
static void DiagnoseCheckerFormalType(const PortDecl& port, bool type_omitted,
                                      bool direction_written, bool is_checker,
                                      DiagEngine& diag) {
  if (!is_checker) return;
  if (type_omitted && direction_written) {
    diag.Error(port.loc,
               std::format("checker formal '{}' has an explicit direction, so "
                           "its type shall not be omitted",
                           port.name),
               Subclause("17.2"));
    return;
  }
  if (port.direction == Direction::kOutput &&
      port.formal_type != PropertyFormalType::kData) {
    diag.Error(port.loc,
               std::format("checker output formal '{}' is declared '{}', a "
                           "type only an input formal can take",
                           port.name, FormalTypeKeyword(port.formal_type)),
               Subclause("17.2"));
  }
}

// §17.2: when a checker formal argument omits its direction, the direction of
// the previous formal is inferred; the first formal defaults to input.
// Module-style ports instead default to inout when no prior direction exists.
static Direction InheritedPortDirection(const PortDecl* prev, bool is_checker) {
  if (prev) return prev->direction;
  return is_checker ? Direction::kInput : Direction::kInout;
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

  if (port.direction == Direction::kNone) {
    port.direction = InheritedPortDirection(prev, is_checker);
  }

  // §17.2: a checker's first formal with its type omitted takes the direction
  // input and the type untyped, and a formal of one of the keyword types has
  // no data type to resolve.
  if (is_checker && !prev && FormalTypeOmitted(port)) {
    port.formal_type = PropertyFormalType::kUntyped;
  }
  if (port.formal_type != PropertyFormalType::kData) return;

  InferImplicitNetForPort(port);

  if (port.data_type.kind == DataTypeKind::kImplicit)
    port.data_type.kind = DataTypeKind::kLogic;
}

void Parser::ParsePortList(ModuleDecl& mod) {
  Expect(TokenKind::kLParen, Subclause("23.2.2"));
  if (Check(TokenKind::kRParen)) {
    Consume();
    return;
  }

  if (Check(TokenKind::kDotStar)) {
    Consume();
    mod.has_wildcard_ports = true;
    Expect(TokenKind::kRParen, Subclause("23.5"));
    return;
  }

  // A.1.3's list_of_ports, the non-ANSI form, is a module's, an interface's
  // and a program's: A.1.8's checker_port_list is checker_port_item alone,
  // whose formal_port_identifier follows a property_formal_type that may be
  // implicit, so `checker c(a, b)` names two formals of the type §17.2 infers
  // rather than two ports declared in the body.
  const bool kIsChecker = mod.decl_kind == ModuleDeclKind::kChecker;
  if (!kIsChecker && (Check(TokenKind::kDot) || Check(TokenKind::kLBrace) ||
                      ParserPortHelpers::LooksLikeNonAnsiPortList(*this))) {
    ParseNonAnsiPortList(mod);
    return;
  }

  ParseOnePortOfList(mod, nullptr, kIsChecker);
  while (Match(TokenKind::kComma)) {
    PortDecl prev = mod.ports.back();

    if (ParserPortHelpers::TryParseBareContinuationPort(*this, mod, prev,
                                                        kIsChecker)) {
      continue;
    }
    ParseOnePortOfList(mod, &prev, kIsChecker);
  }
  Expect(TokenKind::kRParen, Subclause("23.2.2.2"));
}

// One port of an ANSI port list, read, given the direction and type it
// inherits from `prev`, and checked as a checker's formal when the list is a
// checker's: first as written, by Parser::DiagnoseCheckerFormalAsWritten in
// parser_verify.cpp, and then for §17.2's rules on its type.
void Parser::ParseOnePortOfList(ModuleDecl& mod, const PortDecl* prev,
                                bool is_checker) {
  mod.ports.push_back(ParsePortDecl());
  PortDecl& port = mod.ports.back();
  if (is_checker) DiagnoseCheckerFormalAsWritten(port);
  bool type_omitted = FormalTypeOmitted(port);
  bool direction_written = port.direction != Direction::kNone;
  ResolvePortDefaults(port, prev, is_checker);
  DiagnoseCheckerFormalType(port, type_omitted, direction_written, is_checker,
                            diag_);
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
  Expect(TokenKind::kRParen, Subclause("23.2.2.1"));
}

PortDecl Parser::ParsePortDecl() {
  PortDecl port;

  // §A.1.3: each ansi_port_declaration in a list_of_port_declarations may be
  // preceded by attribute_instances, which are the port's (§5.12).
  port.attrs = ParseAttributes();

  port.loc = CurrentLoc();

  Direction dir = TokenToDirection(CurrentToken().kind);
  if (dir != Direction::kNone) {
    port.direction = dir;
    Consume();
  }

  if (ParserPortHelpers::TryParseExplicitNamedPort(*this, port)) {
    return port;
  }

  if (Check(TokenKind::kKwInterface)) {
    ParserPortHelpers::ParseAnsiInterfacePort(*this, port);
    return port;
  }

  if (dir == Direction::kNone && CheckIdentifier() &&
      known_types_.count(CurrentToken().text) == 0) {
    if (ParserPortHelpers::TryParseAnsiModportPort(*this, port)) {
      return port;
    }
    if (ParserPortHelpers::TryParseSimpleInterfacePort(*this, port)) {
      return port;
    }
  }

  if (!ParserPortHelpers::TryParseKeywordFormalType(*this, port)) {
    ParserPortHelpers::ParseTypedPortHead(*this, port, dir);
  }

  auto name_tok = ExpectIdentifier(Subclause("23.2.2.2"));
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
  // §23.5: a `.*` header stands in for the extern declaration's port list. The
  // extern may be non-ANSI (names only), in which case the module body supplies
  // the port directions via non-ANSI port declarations, so accept those here.
  bool non_ansi = HasNonAnsiPorts(mod) || mod.has_wildcard_ports;

  if (Check(TokenKind::kKwTimeunit) || Check(TokenKind::kKwTimeprecision)) {
    ParserPortHelpers::ParseLeadingTimeunitPair(*this, mod);
  }
  while (!Check(TokenKind::kKwEndmodule) && !AtEnd()) {
    if (Match(TokenKind::kSemicolon)) continue;
    if (non_ansi && TryParseBodyPortDecl(mod)) continue;
    ParseModuleItem(mod.items);
  }
  current_module_ = prev_module;
}

// A.1.4's module_item, A.1.6's interface_item and A.1.7's program_item each
// open with `port_declaration ;`, one production in all three bodies, so all
// three read it here: an attributed declaration included, and recorded as an
// item, which makes a timeunits_declaration after it a later one that
// §3.14.2.2 holds to a matching earlier declaration. Answers whether one
// stood.
bool Parser::TryParseBodyPortDecl(ModuleDecl& mod) {
  if (!ParserPortHelpers::TryParseNonAnsiBodyPortDecl(*this, mod)) return false;
  mod.has_body_port_decls = true;
  return true;
}

// Whether a non-ANSI port declaration with direction `dir` and data type
// `dtype` declares a net that its data type does not already say is one.
// §23.2.2.3 (printed page 735) makes an inout declared with no port kind a net
// of the default net type, and mh4 there makes an inout `var` an error, which
// the elaborator reports. An input or output whose data type is implicit holds
// no net or variable type either, and §23.2.2.1 (printed pages 731 and 732)
// makes it a net unless the body declares it again as a variable, which the
// elaborator then reads. A declaration written with `var` holds a variable
// type and is never a net.
static bool NonAnsiPortDeclIsNet(Direction dir, const DataType& dtype,
                                 bool has_var) {
  if (has_var) return false;
  if (dir == Direction::kInout) return true;
  return (dir == Direction::kInput || dir == Direction::kOutput) &&
         dtype.kind == DataTypeKind::kImplicit;
}

void Parser::ParseNonAnsiPortDecls(ModuleDecl& mod,
                                   std::vector<Attribute> attrs) {
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
                "declarations, not the non-ANSI port style",
                Subclause("25.3.3"));
    while (!Check(TokenKind::kSemicolon) && !Check(TokenKind::kKwEndmodule) &&
           !AtEnd())
      Consume();
    Match(TokenKind::kSemicolon);
    return;
  }

  // Syntax 23-3 (§23.2.2.1, printed page 731): an input, output or ref
  // declaration may hold a variable_port_type, which A.2.2.1 lets open with
  // `var` and an optional data type after it.
  bool has_var = Match(TokenKind::kKwVar);
  auto dtype = ParseDataType();
  if (NonAnsiPortDeclIsNet(dir, dtype, has_var)) dtype.is_net = true;

  if (dtype.kind == DataTypeKind::kImplicit && Check(TokenKind::kLBracket)) {
    Consume();
    dtype.packed_dim_left = ParseExpr();
    Expect(TokenKind::kColon, Subclause("23.2.2.1"));
    dtype.packed_dim_right = ParseExpr();
    Expect(TokenKind::kRBracket, Subclause("23.2.2.1"));
  }

  PortDecl shape;
  shape.direction = dir;
  shape.data_type = dtype;
  shape.has_explicit_var = has_var;
  shape.attrs = std::move(attrs);
  do {
    ParserPortHelpers::ApplyNonAnsiPortDecl(*this, mod, shape);
  } while (Match(TokenKind::kComma));
  Expect(TokenKind::kSemicolon, Subclause("23.2.2.1"));
}

}  // namespace delta
