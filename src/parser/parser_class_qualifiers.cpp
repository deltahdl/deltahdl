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
