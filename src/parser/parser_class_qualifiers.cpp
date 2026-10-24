// IEEE 1800-2023 §8.3's class item qualifiers as a class body's parse reads
// them: each `local`, `protected`, `rand`, `randc` and `virtual` consumed
// ahead of the member it qualifies, reported where it repeats or where two
// that exclude each other meet, and, once the member is known, each checked
// against the qualifiers A.1.9 gives that kind of class_item.
//
// These functions are their own translation unit rather than part of
// src/parser/parser_class.cpp, which reached the limit
// assert-no-oversized-source-files enforces when a class body began reading
// a nettype declaration as a class item.

#include <cstdint>
#include <format>

#include "common/diagnostic.h"
#include "lexer/token.h"
#include "parser/ast_class.h"
#include "parser/parser.h"

namespace delta {

bool Parser::TryConsumeClassQualifier(ClassMember* m, TokenKind kw,
                                      bool ClassMember::* flag,
                                      const char* dup_msg) {
  if (!Check(kw)) return false;
  if (m->*flag) diag_.Error(CurrentLoc(), dup_msg, Subclause("8.3"));
  m->*flag = true;
  Consume();
  return true;
}

bool Parser::TryConsumeAccessQualifier(ClassMember* m) {
  if (Check(TokenKind::kKwLocal)) {
    if (m->is_protected)
      diag_.Error(CurrentLoc(),
                  "cannot combine 'local' and 'protected' qualifiers",
                  Subclause("8.3"));
    if (m->is_local)
      diag_.Error(CurrentLoc(), "duplicate 'local' qualifier",
                  Subclause("8.3"));
    m->is_local = true;
    Consume();
    return true;
  }
  if (Check(TokenKind::kKwProtected)) {
    if (m->is_local)
      diag_.Error(CurrentLoc(),
                  "cannot combine 'local' and 'protected' qualifiers",
                  Subclause("8.3"));
    if (m->is_protected)
      diag_.Error(CurrentLoc(), "duplicate 'protected' qualifier",
                  Subclause("8.3"));
    m->is_protected = true;
    Consume();
    return true;
  }
  return false;
}

bool Parser::TryConsumeRandQualifier(ClassMember* m) {
  if (Check(TokenKind::kKwRand)) {
    if (m->is_randc)
      diag_.Error(CurrentLoc(), "cannot combine 'rand' and 'randc' qualifiers",
                  Subclause("8.3"));
    if (m->is_rand)
      diag_.Error(CurrentLoc(), "duplicate 'rand' qualifier", Subclause("8.3"));
    m->is_rand = true;
    Consume();
    return true;
  }
  if (Check(TokenKind::kKwRandc)) {
    if (m->is_rand)
      diag_.Error(CurrentLoc(), "cannot combine 'rand' and 'randc' qualifiers",
                  Subclause("8.3"));
    if (m->is_randc)
      diag_.Error(CurrentLoc(), "duplicate 'randc' qualifier",
                  Subclause("8.3"));
    m->is_randc = true;
    Consume();
    return true;
  }
  return false;
}

// §25.9: 'virtual' is overloaded inside a class body. It begins a virtual
// interface property type only when followed by an interface name ('virtual Bus
// b;') or the explicit 'interface' keyword ('virtual interface Bus b;'); that
// case must be left for ParseDataType. In every other position it is a member
// qualifier (virtual function/task, a nested virtual class, or ahead of further
// method qualifiers such as 'pure virtual protected function'). Peeks one token
// past 'virtual'.
bool Parser::VirtualIsClassQualifier() {
  auto saved = lexer_.SavePos();
  Consume();
  bool is_interface_type =
      Check(TokenKind::kIdentifier) || Check(TokenKind::kKwInterface);
  lexer_.RestorePos(saved);
  return !is_interface_type;
}

bool Parser::TryConsumeVirtualQualifier(ClassMember* m) {
  if (!Check(TokenKind::kKwVirtual) || !VirtualIsClassQualifier()) return false;
  if (m->is_virtual)
    diag_.Error(CurrentLoc(), "duplicate 'virtual' qualifier",
                Subclause("8.3"));
  m->is_virtual = true;
  Consume();
  return true;
}

// A.1.9 gives each kind of class_item its own qualifiers: class_property
// takes `{ property_qualifier }`, rand, randc, static, protected and local,
// and the const form `const { class_item_qualifier }`; class_method takes
// `{ method_qualifier }`, `[ pure ] virtual`, static, protected and local,
// and `extern` before a prototype; A.1.10's constraint_prototype and
// constraint_declaration take extern, pure and static; a nested
// class_declaration opens with `[ virtual ]`; a type_declaration and a
// nettype_declaration are data_declarations and take what a class_property
// takes; and a local_parameter_declaration, a parameter_declaration and a
// covergroup_declaration take none. ParseClassQualifiers reads every qualifier
// before it knows which item follows, so what it read is checked here against
// `allowed`, the set the item admits, and each qualifier outside it is
// reported at the item under A.1.9 and left as it was read.
void Parser::RejectMisplacedClassQualifiers(const ClassMember& member,
                                            uint16_t allowed,
                                            const char* item) {
  struct Qualifier {
    bool present;
    uint16_t bit;
    const char* keyword;
  };
  const Qualifier kQualifiers[] = {
      {member.is_rand, kQualRand, "rand"},
      {member.is_randc, kQualRandc, "randc"},
      {member.is_static, kQualStatic, "static"},
      {member.is_protected, kQualProtected, "protected"},
      {member.is_local, kQualLocal, "local"},
      {member.is_virtual, kQualVirtual, "virtual"},
      {member.is_pure_virtual, kQualPure, "pure"},
      {member.is_const, kQualConst, "const"},
      {member.is_constraint_extern, kQualExtern, "extern"},
  };
  for (const auto& q : kQualifiers) {
    if (!q.present || (allowed & q.bit) != 0) continue;
    diag_.Error(member.loc,
                std::format("'{}' is no qualifier of a {}", q.keyword, item),
                Subclause("A.1.9"));
  }
}

}  // namespace delta
