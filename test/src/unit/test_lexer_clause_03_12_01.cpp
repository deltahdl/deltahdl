#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"

using namespace delta;

namespace {

TEST(CompilationUnitLexing, DollarUnitScopeResolution) {
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

TEST(DesignBuildingBlockLexing, DollarUnitNotScopeResolution) {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  auto fid = mgr.AddFile("<test>", "$unit(arg)");
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  auto t1 = lexer.Next();
  EXPECT_EQ(t1.kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(t1.text, "$unit");
  auto t2 = lexer.Next();
  EXPECT_EQ(t2.kind, TokenKind::kLParen);
}

TEST(DesignBuildingBlockLexing, DollarUnitWithWhitespace) {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  auto fid = mgr.AddFile("<test>", "$unit :: name");
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  auto t1 = lexer.Next();
  EXPECT_EQ(t1.kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(t1.text, "$unit");
  auto t2 = lexer.Next();
  EXPECT_EQ(t2.kind, TokenKind::kColonColon);
  auto t3 = lexer.Next();
  EXPECT_EQ(t3.kind, TokenKind::kIdentifier);
  EXPECT_EQ(t3.text, "name");
}

TEST(CompilationUnitLexing, DollarUnitFollowedByDot) {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  auto fid = mgr.AddFile("<test>", "$unit.foo");
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  auto t1 = lexer.Next();
  EXPECT_EQ(t1.kind, TokenKind::kSystemIdentifier);
  EXPECT_EQ(t1.text, "$unit");
  auto t2 = lexer.Next();
  EXPECT_EQ(t2.kind, TokenKind::kDot);
}

}  // namespace
