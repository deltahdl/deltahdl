#include <cstddef>
#include <cstdint>
#include <format>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "lexer/token.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"
#include "parser/param_port_list.h"
#include "parser/parser.h"
#include "parser/parser_data_decl_internal.h"
#include "parser/parser_headers.h"
#include "parser/parser_prototype_validate.h"
#include "parser/parser_type_name_scope.h"

namespace delta {

struct ParserClassHelpers {
  static bool ParseHead(Parser& p, ModuleDecl* decl, TokenKind keyword,
                        Subclause subclause) {
    p.Expect(keyword, subclause);

    const SourceLoc kLifetimeLoc = p.CurrentLoc();
    decl->is_automatic = p.Match(TokenKind::kKwAutomatic);
    const bool kHasLifetime =
        decl->is_automatic || p.Match(TokenKind::kKwStatic);

    decl->name = p.Expect(TokenKind::kIdentifier, subclause).text;
    p.declared_design_elements_.insert(decl->name);
    p.ParseParamsPortsAndSemicolon(*decl);
    if (kHasLifetime && decl->has_wildcard_ports) {
      p.diag_.Error(
          kLifetimeLoc,
          std::format("{} ( .* ) header takes no lifetime",
                      keyword == TokenKind::kKwInterface ? "an interface"
                                                         : "a program"),
          Subclause("A.1.2"));
    }
    return decl->has_wildcard_ports ||
           (!decl->ports.empty() &&
            decl->ports[0].direction == Direction::kNone);
  }

  static void ParseTail(Parser& p, ModuleDecl* decl, TokenKind end_keyword,
                        Subclause subclause) {
    p.Expect(end_keyword, subclause);
    p.MatchEndLabel(decl->name);
    decl->range.end = p.CurrentLoc();
  }

  static bool ConsumeQualifier(Parser& p, ClassMember* m, bool& proto) {
    if (p.TryConsumeAccessQualifier(m) ||
        p.TryConsumeClassQualifier(m, TokenKind::kKwStatic,
                                   &ClassMember::is_static,
                                   "duplicate 'static' qualifier") ||
        p.TryConsumeVirtualQualifier(m) || p.TryConsumeRandQualifier(m) ||
        p.TryConsumeClassQualifier(m, TokenKind::kKwConst,
                                   &ClassMember::is_const,
                                   "duplicate 'const' qualifier")) {
      return true;
    }
    if (p.Match(TokenKind::kKwPure)) {
      m->is_pure_virtual = true;
      proto = true;
      return true;
    }
    if (!p.Match(TokenKind::kKwExtern)) return false;
    proto = true;
    m->is_constraint_extern = true;
    return true;
  }

  static void NoteQualifierOrder(Parser& p, ClassMember* m, TokenKind kw,
                                 int index, bool& extern_first) {
    if (kw == TokenKind::kKwExtern) {
      extern_first = index == 0;
      m->extern_follows_qualifier = !extern_first;
    } else if (kw == TokenKind::kKwPure) {
      m->pure_apart_from_virtual = !p.Check(TokenKind::kKwVirtual);
      m->pure_follows_qualifier = index > 0 && !extern_first;
    } else if (kw == TokenKind::kKwRand || kw == TokenKind::kKwRandc) {
      if (m->is_const) m->random_follows_const = true;
    }
  }

  static void RejectMethodQualifierOrder(Parser& p, const ClassMember& m) {
    if (m.extern_follows_qualifier) {
      p.diag_.Error(m.loc,
                    "'extern' is written after another qualifier; it stands "
                    "before every qualifier of a method",
                    Subclause("A.1.9"));
    }
    if (m.is_virtual && m.pure_apart_from_virtual) {
      p.diag_.Error(m.loc,
                    "'pure' is written apart from 'virtual'; it stands "
                    "directly before it",
                    Subclause("A.1.9"));
    }
  }

  static void RejectPureVirtualPrototypeOrder(Parser& p, const ClassMember& m) {
    if (!m.pure_follows_qualifier || m.pure_apart_from_virtual) return;
    p.diag_.Error(m.loc,
                  "a pure virtual method prototype opens with 'pure virtual'; "
                  "another qualifier is written before it",
                  Subclause("A.1.9"));
  }

  static void RejectPropertyQualifiers(Parser& p, const ClassMember& m) {
    p.RejectMisplacedClassQualifiers(
        m,
        Parser::kQualRand | Parser::kQualRandc | Parser::kQualStatic |
            Parser::kQualProtected | Parser::kQualLocal | Parser::kQualConst,
        "class property");
    if (!m.random_follows_const) return;
    p.diag_.Error(m.loc,
                  "a random qualifier is written after 'const'; neither form "
                  "of a class property writes one there",
                  Subclause("A.1.9"));
  }

  static void ParseTypeMember(Parser& p, std::vector<ClassMember*>& members,
                              ClassMember* member, bool is_nettype) {
    p.RejectMisplacedClassQualifiers(
        *member,
        Parser::kQualRand | Parser::kQualRandc | Parser::kQualStatic |
            Parser::kQualProtected | Parser::kQualLocal,
        is_nettype ? "nettype declaration" : "type declaration");
    member->kind = ClassMemberKind::kTypedef;
    member->typedef_item = is_nettype ? p.ParseNettypeDecl() : p.ParseTypedef();
    member->name = member->typedef_item->name;
    members.push_back(member);
  }

  static void CheckInterfaceClassItems(Parser& p, const ClassDecl& decl,
                                       size_t first) {
    if (!decl.is_interface) return;
    for (size_t i = first; i < decl.members.size(); ++i) {
      const ClassMember& m = *decl.members[i];
      if (m.kind == ClassMemberKind::kTypedef &&
          m.typedef_item->kind == ModuleItemKind::kNettypeDecl) {
        p.diag_.Error(m.loc,
                      "a nettype declaration is no item of an interface class",
                      Subclause("A.1.9"));
      } else if (m.kind == ClassMemberKind::kMethod) {
        p.RejectMisplacedClassQualifiers(
            m,
            static_cast<uint16_t>(~(Parser::kQualProtected |
                                    Parser::kQualLocal | Parser::kQualExtern)),
            "method of an interface class");
      } else if (m.kind == ClassMemberKind::kTypedef &&
                 !m.typedef_item->is_localparam) {
        p.RejectMisplacedClassQualifiers(
            m,
            static_cast<uint16_t>(
                ~(Parser::kQualRand | Parser::kQualRandc | Parser::kQualStatic |
                  Parser::kQualProtected | Parser::kQualLocal)),
            "type declaration in an interface class");
      }
    }
  }
};

ModuleDecl* Parser::ParseInterfaceDecl() {
  auto* decl = arena_.Create<ModuleDecl>();
  TypeNameScope type_scope(*this);
  decl->decl_kind = ModuleDeclKind::kInterface;
  decl->range.start = CurrentLoc();
  bool non_ansi = ParserClassHelpers::ParseHead(
      *this, decl, TokenKind::kKwInterface, Subclause("25.3"));

  auto* prev_module = current_module_;
  current_module_ = decl;
  while (!Check(TokenKind::kKwEndinterface) && !AtEnd()) {
    if (NoteItemAndMatchNull(decl->has_read_body_item)) continue;
    if (Check(TokenKind::kKwModport)) {
      ParseModportDecl(decl->modports);
    } else if (!non_ansi || !TryParseBodyPortDecl(*decl)) {
      ParseModuleItem(decl->items);
    }
  }
  current_module_ = prev_module;
  ParserClassHelpers::ParseTail(*this, decl, TokenKind::kKwEndinterface,
                                Subclause("25.3"));
  return decl;
}

ModuleDecl* Parser::ParseProgramDecl() {
  auto* decl = arena_.Create<ModuleDecl>();
  TypeNameScope type_scope(*this);
  decl->decl_kind = ModuleDeclKind::kProgram;
  decl->range.start = CurrentLoc();
  bool non_ansi = ParserClassHelpers::ParseHead(
      *this, decl, TokenKind::kKwProgram, Subclause("24.3"));

  auto* prev_module = current_module_;
  current_module_ = decl;
  while (!Check(TokenKind::kKwEndprogram) && !AtEnd()) {
    if (NoteItemAndMatchNull(decl->has_read_body_item)) continue;
    if (!non_ansi || !TryParseBodyPortDecl(*decl)) ParseModuleItem(decl->items);
  }
  current_module_ = prev_module;
  ParserClassHelpers::ParseTail(*this, decl, TokenKind::kKwEndprogram,
                                Subclause("24.3"));
  return decl;
}

void Parser::AdoptBaseClassTypeNames(const ClassDecl* decl) {
  auto adopt = [&](std::string_view base) {
    auto it = class_types_.find(base);
    if (it != class_types_.end()) AdoptTypeNames(it->second);
  };
  adopt(decl->base_class);
  for (const auto& iface : decl->extends_interfaces) adopt(iface.name);
  for (const auto& iface : decl->implements_types) adopt(iface.name);
}

void Parser::AdoptMethodClassTypeNames(std::string_view class_name) {
  auto it = class_types_.find(class_name);
  if (it != class_types_.end()) AdoptTypeNames(it->second);
}

ClassDecl* Parser::ParseClassDecl() {
  auto* decl = arena_.Create<ClassDecl>();
  decl->range.start = CurrentLoc();
  ParserClassHeaderHelpers::ParseHeadKeywords(*this, decl);
  decl->name = Expect(TokenKind::kIdentifier, Subclause("8.3")).text;
  known_types_.insert(decl->name);

  TypeNameScope type_scope(*this);

  if (Check(TokenKind::kHash)) {
    Consume();
    Expect(TokenKind::kLParen, Subclause("8.25"));
    ParamPortList out{decl->params, decl->type_param_names,
                      decl->localparam_port_names, &decl->param_types,
                      &decl->param_port_unpacked_dims};
    ParseParamPortDecls(out);
    Expect(TokenKind::kRParen, Subclause("8.25"));
  }

  if (Match(TokenKind::kKwExtends)) ParseClassExtendsClause(decl, false);

  if (Match(TokenKind::kKwImplements)) ParseClassExtendsClause(decl, true);
  Expect(TokenKind::kSemicolon, Subclause("8.3"));

  AdoptBaseClassTypeNames(decl);
  ++class_body_depth_;
  while (!Check(TokenKind::kKwEndclass) && !AtEnd()) {
    if (Match(TokenKind::kSemicolon)) continue;
    auto before = lexer_.SavePos().pos;
    const size_t kFirstNew = decl->members.size();
    ParseClassMembers(decl->members);
    ParserClassHelpers::CheckInterfaceClassItems(*this, *decl, kFirstNew);

    if (lexer_.SavePos().pos == before) Consume();
  }
  --class_body_depth_;
  class_types_[decl->name] = type_scope.NamesAddedSoFar();
  Expect(TokenKind::kKwEndclass, Subclause("8.3"));
  MatchEndLabel(decl->name);
  decl->range.end = CurrentLoc();
  return decl;
}

bool Parser::ParseClassQualifiers(ClassMember* m) {
  bool proto = false;
  bool extern_first = false;
  for (int index = 0;; ++index) {
    const TokenKind kKeyword = CurrentToken().kind;
    if (!ParserClassHelpers::ConsumeQualifier(*this, m, proto)) break;
    ParserClassHelpers::NoteQualifierOrder(*this, m, kKeyword, index,
                                           extern_first);
  }
  return proto;
}

void Parser::ValidateClassMethod(ClassMember* member) {
  if (member->method->is_static) {
    diag_.Error(member->method->loc,
                "class method shall not have static lifetime",
                Subclause("8.6"));
  }

  if (member->is_static && member->is_virtual &&
      member->method->name != "new") {
    diag_.Error(member->method->loc,
                "this method is declared both static and virtual, which no "
                "method can be",
                Subclause("8.10"));
  }
  if (member->is_static) member->method->is_static_method = true;
}

void Parser::ValidateConstructorQualifiers(ClassMember* member) {
  if (member->method->name != "new") return;
  if (member->is_static) {
    diag_.Error(member->method->loc,
                "'new' is declared static here, which a constructor never is",
                Subclause("8.7"));
  }
  if (member->is_virtual) {
    diag_.Error(member->method->loc,
                "'new' is declared virtual here, which a constructor never is",
                Subclause("8.7"));
  }
}

void Parser::RejectPureVirtualMethodBody(const ClassMember* member,
                                         bool is_func) {
  if (!member->is_pure_virtual) return;
  TokenKind terminator =
      is_func ? TokenKind::kKwEndfunction : TokenKind::kKwEndtask;
  auto saved = lexer_.SavePos();
  bool found = false;
  while (!AtEnd() && !Check(TokenKind::kKwEndclass) &&
         !Check(TokenKind::kKwFunction) && !Check(TokenKind::kKwTask)) {
    if (Check(terminator)) {
      found = true;
      break;
    }
    Consume();
  }
  if (!found) {
    lexer_.RestorePos(saved);
    ParserClassHelpers::RejectPureVirtualPrototypeOrder(*this, *member);
    return;
  }
  diag_.Error(member->method->loc,
              "a pure virtual method shall not have a body; 'pure' is "
              "indicated by not providing one",
              Subclause("8.21"));
  Consume();
  if (Match(TokenKind::kColon)) Match(TokenKind::kIdentifier);
}

bool Parser::TryParseMethodOrConstraint(std::vector<ClassMember*>& members,
                                        ClassMember* member, bool proto) {
  bool is_func = Check(TokenKind::kKwFunction);
  if (is_func || Check(TokenKind::kKwTask)) {
    RejectMisplacedClassQualifiers(*member,
                                   kQualStatic | kQualProtected | kQualLocal |
                                       kQualVirtual | kQualPure | kQualExtern,
                                   "class method");
    if (member->is_pure_virtual && !member->is_virtual) {
      diag_.Error(member->loc,
                  "'pure' qualifies 'virtual'; a method is pure virtual or "
                  "virtual",
                  Subclause("A.1.9"));
    }
    ParserClassHelpers::RejectMethodQualifierOrder(*this, *member);
    member->kind = ClassMemberKind::kMethod;
    member->method = is_func ? ParseFunctionDecl(proto) : ParseTaskDecl(proto);
    if (proto) ValidateClassMethodPrototype(diag_, member->method);
    member->name = member->method->name;
    ValidateClassMethod(member);
    if (is_func) ValidateConstructorQualifiers(member);
    if (proto && !member->is_pure_virtual) member->method->is_extern = true;
    RejectPureVirtualMethodBody(member, is_func);
    members.push_back(member);
    return true;
  }
  if (Check(TokenKind::kKwConstraint)) {
    RejectMisplacedClassQualifiers(
        *member, kQualStatic | kQualPure | kQualExtern, "class constraint");
    members.push_back(ParseConstraintStub(member));
    return true;
  }
  return false;
}

static bool IsLocalTypeParam(const ModuleItem* item) {
  return item->data_type.kind == DataTypeKind::kVoid && item->is_localparam &&
         item->typedef_type.kind != DataTypeKind::kImplicit &&
         item->forward_type_kind == DataTypeKind::kImplicit;
}

void Parser::ParseClassParameterMembers(std::vector<ClassMember*>& members,
                                        ClassMember* member) {
  std::vector<ModuleItem*> param_items;
  ParseParamDecl(param_items);
  for (size_t i = 0; i < param_items.size(); ++i) {
    auto* m = (i == 0) ? member : arena_.Create<ClassMember>();
    m->name = param_items[i]->name;
    if (IsLocalTypeParam(param_items[i])) {
      param_items[i]->kind = ModuleItemKind::kTypedef;
      m->kind = ClassMemberKind::kTypedef;
      m->typedef_item = param_items[i];
      members.push_back(m);
      continue;
    }
    m->kind = ClassMemberKind::kProperty;
    m->is_param = true;
    m->data_type = param_items[i]->data_type;
    m->unpacked_dims = param_items[i]->unpacked_dims;
    m->init_expr = param_items[i]->init_expr;
    members.push_back(m);
  }
}

bool Parser::TryParseKeywordClassMember(std::vector<ClassMember*>& members,
                                        ClassMember* member, bool proto) {
  if (TryParseMethodOrConstraint(members, member, proto)) return true;
  const bool kNettype = Check(TokenKind::kKwNettype);
  if (kNettype || Check(TokenKind::kKwTypedef)) {
    ParserClassHelpers::ParseTypeMember(*this, members, member, kNettype);
    return true;
  }
  if (Check(TokenKind::kKwParameter) || Check(TokenKind::kKwLocalparam)) {
    RejectMisplacedClassQualifiers(*member, 0, "parameter declaration");
    ParseClassParameterMembers(members, member);
    return true;
  }
  if (IsAtClassDecl()) {
    RejectMisplacedClassQualifiers(*member, kQualVirtual,
                                   "nested class declaration");
    member->kind = ClassMemberKind::kClassDecl;
    member->nested_class = ParseClassDecl();
    if (member->is_virtual) member->nested_class->is_virtual = true;
    member->name = member->nested_class->name;
    members.push_back(member);
    return true;
  }
  if (Check(TokenKind::kKwCovergroup)) {
    RejectMisplacedClassQualifiers(*member, 0, "covergroup declaration");
    member->kind = ClassMemberKind::kCovergroup;
    std::vector<ModuleItem*> temp;
    ParseCovergroupDecl(temp);
    if (!temp.empty()) {
      member->name = temp[0]->name;
      member->covergroup_extends_base = temp[0]->covergroup_extends_base;
      member->covergroup = temp[0]->covergroup;
    }
    members.push_back(member);
    return true;
  }
  return false;
}

void Parser::ParseClassMembers(std::vector<ClassMember*>& members) {
  std::vector<Attribute> attrs = ParseAttributes();

  if (Check(TokenKind::kKwImport)) {
    SourceLoc import_loc = CurrentLoc();
    Consume();
    if (Check(TokenKind::kStringLiteral)) {
      diag_.Error(import_loc,
                  "DPI import declaration is not allowed in class scope",
                  Subclause("35.5.4"));
    } else {
      diag_.Error(import_loc,
                  "package import declaration is not allowed in class scope",
                  Subclause("26.3"));
    }
    while (!Check(TokenKind::kSemicolon) && !AtEnd()) Consume();
    Match(TokenKind::kSemicolon);
    return;
  }
  if (Check(TokenKind::kKwExport)) {
    diag_.Error(CurrentLoc(),
                "DPI export declaration is not allowed in class scope; "
                "class member functions cannot be exported",
                Subclause("35.7"));
    while (!Check(TokenKind::kSemicolon) && !AtEnd()) Consume();
    Match(TokenKind::kSemicolon);
    return;
  }
  if (AtClockingDecl()) {
    RejectClockingDecl(
        "a class body cannot hold a clocking block; only a module, an "
        "interface, a checker or a program body can");
    return;
  }
  auto* member = arena_.Create<ClassMember>();
  member->loc = CurrentLoc();
  member->attrs = std::move(attrs);
  bool proto = ParseClassQualifiers(member);

  if (TryParseKeywordClassMember(members, member, proto)) return;

  ParserClassHelpers::RejectPropertyQualifiers(*this, *member);
  DataType dtype = ParserDataDeclHelpers::ReadClassPropertyType(*this);
  member->kind = ClassMemberKind::kProperty;
  member->data_type = dtype;
  member->name = Expect(TokenKind::kIdentifier, Subclause("8.5")).text;
  ParseUnpackedDims(member->unpacked_dims);
  if (Match(TokenKind::kEq)) member->init_expr = ParseExpr();
  members.push_back(member);
  ParseExtraPropertyDecls(members, member, dtype);
  Expect(TokenKind::kSemicolon, Subclause("8.5"));
}

void Parser::ParseExtraPropertyDecls(std::vector<ClassMember*>& members,
                                     const ClassMember* first,
                                     const DataType& dtype) {
  while (Match(TokenKind::kComma)) {
    auto* extra = arena_.Create<ClassMember>();
    extra->loc = CurrentLoc();
    extra->kind = ClassMemberKind::kProperty;
    extra->data_type = dtype;
    extra->is_rand = first->is_rand;
    extra->is_randc = first->is_randc;
    extra->is_static = first->is_static;
    extra->is_const = first->is_const;
    extra->name = Expect(TokenKind::kIdentifier, Subclause("8.5")).text;
    ParseUnpackedDims(extra->unpacked_dims);
    if (Match(TokenKind::kEq)) extra->init_expr = ParseExpr();
    members.push_back(extra);
  }
}

namespace {

struct ConstraintTokenContext {
  bool prev_was_qualifier;
  bool next_is_lparen;
  bool next_is_dot;
  bool next_is_coloncolon;
};

void RecordConstraintTokenRefs(ClassMember* member, const Token& tok,
                               const ConstraintTokenContext& ctx,
                               bool& in_soft) {
  if (tok.kind == TokenKind::kIdentifier && !ctx.prev_was_qualifier &&
      ctx.next_is_lparen) {
    ConstraintFunctionCallRef ref;
    ref.callee = tok.text;
    ref.loc = tok.loc;
    if (member) member->constraint_function_call_refs.push_back(ref);
  }
  if (in_soft && tok.kind == TokenKind::kIdentifier &&
      !ctx.prev_was_qualifier && !ctx.next_is_lparen && !ctx.next_is_dot &&
      !ctx.next_is_coloncolon) {
    if (member) {
      ConstraintSoftVarRef sref;
      sref.name = tok.text;
      sref.loc = tok.loc;
      member->constraint_soft_refs.push_back(sref);
    }
  }
  if (tok.kind == TokenKind::kSemicolon) in_soft = false;
}

void ApplyConstraintStructuralToken(TokenKind kind, int& depth, bool& in_soft) {
  switch (kind) {
    case TokenKind::kLBrace:
      ++depth;
      break;
    case TokenKind::kRBrace:
      --depth;
      break;
    case TokenKind::kKwSoft:
      in_soft = true;
      break;
    default:
      break;
  }
}

bool LeafClosesQualifier(const Token& tok) {
  return tok.kind == TokenKind::kDot || tok.kind == TokenKind::kColonColon;
}

}  // namespace

bool Parser::ParseConstraintHeader(ClassMember* member) {
  if (Match(TokenKind::kColon)) {
    if (Match(TokenKind::kKwInitial)) {
      member->is_constraint_initial = true;
    } else if (Match(TokenKind::kKwExtends)) {
      member->is_constraint_extends = true;
    } else if (Match(TokenKind::kKwFinal)) {
      member->is_constraint_final = true;
    }
  }
  if (Match(TokenKind::kColon)) {
    if (Match(TokenKind::kKwFinal)) member->is_constraint_final = true;
  }
  member->name = Expect(TokenKind::kIdentifier, Subclause("18.5")).text;

  if (Match(TokenKind::kSemicolon)) {
    member->is_constraint_prototype = true;
    return true;
  }
  Expect(TokenKind::kLBrace, Subclause("18.5"));
  return false;
}

bool Parser::ScanConstraintBodyToken(ClassMember* member, int& depth,
                                     bool& in_soft, bool carried_qualifier) {
  TokenKind kind = CurrentToken().kind;
  if (kind == TokenKind::kKwForeach) {
    CheckForeachConstraintHeader(member);
    return false;
  }
  if (kind == TokenKind::kKwSolve) {
    CheckSolveBeforeConstraint(member);
    return false;
  }
  if (kind == TokenKind::kKwDist) {
    Consume();
    CheckDistSet();
    if (!AtEnd() && !Check(TokenKind::kSemicolon) &&
        !Check(TokenKind::kRBrace)) {
      diag_.Error(CurrentLoc(),
                  "a dist expression may not appear within another expression",
                  Subclause("18.5"));
    }
    return false;
  }
  if (kind == TokenKind::kKwDisable) {
    CaptureDisableSoftConstraint(member);
    return false;
  }
  if (kind == TokenKind::kKwSoft || kind == TokenKind::kLBrace ||
      kind == TokenKind::kRBrace) {
    Consume();
    ApplyConstraintStructuralToken(kind, depth, in_soft);
    return false;
  }
  Token t = CurrentToken();
  CheckConstraintExprToken(t);
  Consume();
  RecordConstraintTokenRefs(
      member, t,
      ConstraintTokenContext{carried_qualifier, Check(TokenKind::kLParen),
                             Check(TokenKind::kDot),
                             Check(TokenKind::kColonColon)},
      in_soft);
  return LeafClosesQualifier(t);
}

}  // namespace delta
