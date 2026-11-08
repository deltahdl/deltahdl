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
#include "parser/parser_data_decl_internal.h"
#include "parser/parser_dpi_validate.h"
#include "parser/parser_headers.h"
#include "parser/parser_token_skips.h"

namespace delta {

static void ResolvePortDefaults(PortDecl& port, const PortDecl* prev,
                                bool is_checker);

struct ParserPortHelpers {
  static void ApplyNonAnsiPortDecl(Parser& p, ModuleDecl& mod,
                                   const PortDecl& shape) {
    auto loc = p.CurrentLoc();
    auto name = p.Expect(TokenKind::kIdentifier, Subclause("23.2.2.1")).text;
    std::vector<Expr*> dims;
    p.ParseUnpackedDims(dims);
    Expr* init = p.Match(TokenKind::kEq) ? p.ParseExpr() : nullptr;
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
      port.default_value = init;
    }
    if (found) return;
    PortDecl np = shape;
    np.name = name;
    np.unpacked_dims = dims;
    np.default_value = init;
    np.loc = loc;
    if (mod.has_wildcard_ports) {
      mod.ports.push_back(np);
    } else {
      mod.port_expr_objects.push_back(np);
    }
  }

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

  static void ParseAnsiInterfacePort(Parser& p, PortDecl& port) {
    p.Consume();
    port.is_interface_port = true;
    if (p.Match(TokenKind::kDot)) {
      port.data_type.modport_name =
          p.ExpectIdentifier(Subclause("25.3.3")).text;
    }
    port.name = p.ExpectIdentifier(Subclause("25.3.3")).text;
    p.ParseUnpackedDims(port.unpacked_dims);
    if (p.Match(TokenKind::kEq)) port.default_value = p.ParseExpr();
  }

  static void FinishAnsiModportPort(Parser& p, PortDecl& port,
                                    std::string_view iface_name,
                                    std::string_view modport_name) {
    port.data_type.kind = DataTypeKind::kNamed;
    port.data_type.type_name = iface_name;
    port.data_type.modport_name = modport_name;
    port.name = p.ExpectIdentifier(Subclause("25.5")).text;
    p.ParseUnpackedDims(port.unpacked_dims);
    if (p.Match(TokenKind::kEq)) port.default_value = p.ParseExpr();
  }

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

  static bool TryParseAnsiModportPort(Parser& p, PortDecl& port) {
    auto saved = p.lexer_.SavePos();
    if (TryMatchAnsiModportPort(p, port)) return true;
    p.lexer_.RestorePos(saved);
    return false;
  }

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

  static bool TryParseExplicitNamedPort(Parser& p, PortDecl& port) {
    if (!p.Check(TokenKind::kDot)) return false;
    port.is_explicit_named = true;
    p.Consume();
    port.name = p.ExpectIdentifier(Subclause("23.2.2.2")).text;
    p.Expect(TokenKind::kLParen, Subclause("23.2.2.2"));
    if (!p.Check(TokenKind::kRParen)) {
      port.port_expr = p.ParseExpr();
    }
    p.Expect(TokenKind::kRParen, Subclause("23.2.2.2"));
    return true;
  }

  static DataType ParsePortDataTypeBody(Parser& p, bool has_var) {
    DataType dtype;
    if (p.Check(TokenKind::kKwStruct) || p.Check(TokenKind::kKwUnion)) {
      dtype = p.ParseStructOrUnionType();
      p.ParsePackedDims(dtype);
      return dtype;
    }
    if (p.Check(TokenKind::kKwEnum)) return p.ParseEnumType();
    if (ParserDataDeclHelpers::ReadKeyedTypeReference(p, dtype, has_var, true))
      return dtype;
    return p.ParseDeclaredDataType();
  }

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

  static void ParseAnsiPortDataType(Parser& p, PortDecl& port) {
    if (p.Match(TokenKind::kKwVar)) {
      port.has_explicit_var = true;
      port.data_type = ParsePortDataTypeBody(p, true);
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
    port.data_type = ParsePortDataTypeBody(p, false);
  }

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

  static bool LooksLikeForwardNamedType(Parser& p, Direction dir) {
    if (dir == Direction::kNone || !p.CheckIdentifier()) return false;
    if (p.known_types_.count(p.CurrentToken().text) != 0) return false;
    auto saved = p.lexer_.SavePos();
    p.Consume();
    bool type_then_name = p.CheckIdentifier();
    p.lexer_.RestorePos(saved);
    return type_then_name;
  }

  static void ParsePortType(Parser& p, PortDecl& port, Direction dir) {
    if (LooksLikeForwardNamedType(p, dir)) {
      port.data_type = p.ParseNamedType();
    } else {
      ParseAnsiPortDataType(p, port);
    }
  }

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
    if (p.Match(TokenKind::kEq)) {
      port.default_value =
          is_checker ? p.ParseCheckerFormalDefault() : p.ParseExpr();
    }
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
  for (size_t i = kFirstSite; i < time_literals_.size(); ++i) {
    time_literals_[i] =
        TimeLiteralSite{time_literals_[i].literal, &decl, nullptr};
  }
}

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

static bool FormalTypeOmitted(const PortDecl& port) {
  return port.formal_type == PropertyFormalType::kData &&
         port.data_type.kind == DataTypeKind::kImplicit &&
         !port.data_type.is_signed && !port.data_type.packed_dim_left;
}

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

void Parser::ParseOnePortOfList(ModuleDecl& mod, const PortDecl* prev,
                                bool is_checker) {
  mod.ports.push_back(ParsePortDecl(is_checker));
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

PortDecl Parser::ParsePortDecl(bool is_checker) {
  PortDecl port;

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
    port.default_value = is_checker ? ParseCheckerFormalDefault() : ParseExpr();
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
  bool non_ansi = HasNonAnsiPorts(mod) || mod.has_wildcard_ports;

  if (Check(TokenKind::kKwTimeunit) || Check(TokenKind::kKwTimeprecision)) {
    ParserPortHelpers::ParseLeadingTimeunitPair(*this, mod);
  }
  while (!Check(TokenKind::kKwEndmodule) && !AtEnd()) {
    if (NoteItemAndMatchNull(mod.has_read_body_item)) continue;
    if (non_ansi && TryParseBodyPortDecl(mod)) continue;
    ParseModuleItem(mod.items);
  }
  current_module_ = prev_module;
}

bool Parser::TryParseBodyPortDecl(ModuleDecl& mod) {
  return ParserPortHelpers::TryParseNonAnsiBodyPortDecl(*this, mod);
}

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

  bool has_var = Match(TokenKind::kKwVar);
  DataType dtype;
  bool is_type_ref = ParserDataDeclHelpers::ReadKeyedTypeReference(
      *this, dtype, has_var, true);
  if (!is_type_ref) dtype = ParseDeclaredDataType();
  if (NonAnsiPortDeclIsNet(dir, dtype, has_var)) dtype.is_net = true;

  if (dtype.kind == DataTypeKind::kImplicit && !is_type_ref)
    ParsePackedDims(dtype);

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
