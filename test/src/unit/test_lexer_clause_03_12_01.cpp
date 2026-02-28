// §3.12.1: Compilation units

#include <gtest/gtest.h>

#include <string>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "common/arena.h"

using namespace delta;

namespace {

// 9. $unit:: scope resolution operator — used for disambiguation.
// $unit is lexed as a system identifier; $unit::name is the syntax.
TEST(ParserClause03, Cl3_12_1_DollarUnitScopeResolution) {
  // The LRM example: b = 5 + $unit::b;
  // $unit is a kSystemIdentifier token; :: is kColonColon.
  // This tests that the lexer correctly produces these tokens.
  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  auto fid = mgr.AddFile("<test>", "$unit::b");
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  auto t1 = lexer.Next();
  EXPECT_EQ(t1.kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(t1.text, "$unit");
  auto t2 = lexer.Next();
  EXPECT_EQ(t2.kind, TokenKind::kColonColon);
  auto t3 = lexer.Next();
  EXPECT_EQ(t3.kind, TokenKind::kIdentifier);
  EXPECT_EQ(t3.text, "b");
}

}  // namespace
