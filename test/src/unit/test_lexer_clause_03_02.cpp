// §3.2: A design element is a SystemVerilog module, program, interface,
// checker, package, primitive, or configuration. These constructs are
// introduced by the keywords module, program, interface, checker, package,
// primitive, and config, respectively. The lexer recognises each of those
// seven keywords as a distinct keyword token.

#include "fixture_lexer.h"

using namespace delta;

namespace {

TEST(DesignElementLexing, ModuleKeywordRecognised) {
  auto r = LexOne("module");
  EXPECT_EQ(r.token.kind, TokenKind::kKwModule);
}

TEST(DesignElementLexing, ProgramKeywordRecognised) {
  auto r = LexOne("program");
  EXPECT_EQ(r.token.kind, TokenKind::kKwProgram);
}

TEST(DesignElementLexing, InterfaceKeywordRecognised) {
  auto r = LexOne("interface");
  EXPECT_EQ(r.token.kind, TokenKind::kKwInterface);
}

TEST(DesignElementLexing, CheckerKeywordRecognised) {
  auto r = LexOne("checker");
  EXPECT_EQ(r.token.kind, TokenKind::kKwChecker);
}

TEST(DesignElementLexing, PackageKeywordRecognised) {
  auto r = LexOne("package");
  EXPECT_EQ(r.token.kind, TokenKind::kKwPackage);
}

TEST(DesignElementLexing, PrimitiveKeywordRecognised) {
  auto r = LexOne("primitive");
  EXPECT_EQ(r.token.kind, TokenKind::kKwPrimitive);
}

TEST(DesignElementLexing, ConfigKeywordRecognised) {
  auto r = LexOne("config");
  EXPECT_EQ(r.token.kind, TokenKind::kKwConfig);
}

TEST(DesignElementLexing, AllSevenKeywordsAreDistinctTokenKinds) {
  // §3.2 enumerates seven distinct introducer keywords; the lexer shall map
  // each to its own TokenKind so the parser can dispatch unambiguously.
  auto m = LexOne("module").token.kind;
  auto p = LexOne("program").token.kind;
  auto i = LexOne("interface").token.kind;
  auto ch = LexOne("checker").token.kind;
  auto pk = LexOne("package").token.kind;
  auto pr = LexOne("primitive").token.kind;
  auto cf = LexOne("config").token.kind;

  TokenKind kinds[] = {m, p, i, ch, pk, pr, cf};
  for (size_t a = 0; a < 7; ++a) {
    for (size_t b = a + 1; b < 7; ++b) {
      EXPECT_NE(kinds[a], kinds[b]);
    }
  }
}

}  // namespace
