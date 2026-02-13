#include <gtest/gtest.h>

#include <cstring>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "parser/ast.h"
#include "simulation/eval.h"
#include "simulation/sim_context.h"

using namespace delta;

// =============================================================================
// Helper: extract a std::string from a Logic4Vec (string encoding)
// =============================================================================

static std::string VecToString(const Logic4Vec& vec) {
  std::string result;
  uint64_t v = vec.ToUint64();
  uint32_t nbytes = (vec.width + 7) / 8;
  for (uint32_t i = nbytes; i > 0; --i) {
    auto ch = static_cast<char>((v >> ((i - 1) * 8)) & 0xFF);
    if (ch != 0) result += ch;
  }
  return result;
}

// =============================================================================
// Test fixture: sets up SimContext with a string variable
// =============================================================================

struct StringFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};

  // Create a string variable and store the given string value.
  Variable* CreateStringVar(std::string_view var_name, std::string_view value) {
    uint32_t width = static_cast<uint32_t>(value.size()) * 8;
    if (width == 0) width = 8;
    auto* var = ctx.CreateVariable(var_name, width);
    var->value = MakeLogic4Vec(arena, width);
    for (size_t i = 0; i < value.size(); ++i) {
      auto byte_idx = static_cast<uint32_t>(value.size() - 1 - i);
      uint32_t word = (byte_idx * 8) / 64;
      uint32_t bit = (byte_idx * 8) % 64;
      var->value.words[word].aval |=
          static_cast<uint64_t>(static_cast<unsigned char>(value[i])) << bit;
    }
    ctx.RegisterStringVariable(var_name);
    return var;
  }

  // Build a method call expression: var_name.method_name(args...)
  Expr* MakeMethodCall(std::string_view var_name, std::string_view method_name,
                       std::vector<Expr*> args = {}) {
    auto* id = arena.Create<Expr>();
    id->kind = ExprKind::kIdentifier;
    id->text = var_name;

    auto* member = arena.Create<Expr>();
    member->kind = ExprKind::kIdentifier;
    member->text = method_name;

    auto* access = arena.Create<Expr>();
    access->kind = ExprKind::kMemberAccess;
    access->lhs = id;
    access->rhs = member;

    auto* call = arena.Create<Expr>();
    call->kind = ExprKind::kCall;
    call->lhs = access;
    call->args = std::move(args);
    return call;
  }

  Expr* MakeIntLiteral(uint64_t val) {
    auto* lit = arena.Create<Expr>();
    lit->kind = ExprKind::kIntegerLiteral;
    lit->int_val = val;
    return lit;
  }

  Expr* MakeStringLiteral(std::string_view text) {
    std::string quoted = "\"" + std::string(text) + "\"";
    char* buf = arena.AllocString(quoted.c_str(), quoted.size());
    auto* lit = arena.Create<Expr>();
    lit->kind = ExprKind::kStringLiteral;
    lit->text = std::string_view(buf, quoted.size());
    return lit;
  }
};

// =============================================================================
// §6.16.1: len() -- returns the length of the string
// =============================================================================

TEST(StringMethods, LenEmpty) {
  StringFixture f;
  f.CreateStringVar("s", "");
  auto* call = f.MakeMethodCall("s", "len");
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(StringMethods, LenBasic) {
  StringFixture f;
  f.CreateStringVar("s", "hello");
  auto* call = f.MakeMethodCall("s", "len");
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 5u);
}

// =============================================================================
// §6.16.2: putc(i, c) -- replace byte at index i
// =============================================================================

TEST(StringMethods, Putc) {
  StringFixture f;
  auto* var = f.CreateStringVar("s", "hello");
  auto* call = f.MakeMethodCall("s", "putc",
                                {f.MakeIntLiteral(0), f.MakeIntLiteral('H')});
  EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(VecToString(var->value), "Hello");
}

// =============================================================================
// §6.16.3: getc(i) -- return byte at index i
// =============================================================================

TEST(StringMethods, Getc) {
  StringFixture f;
  f.CreateStringVar("s", "hello");
  auto* call = f.MakeMethodCall("s", "getc", {f.MakeIntLiteral(1)});
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), static_cast<uint64_t>('e'));
}

// =============================================================================
// §6.16.4: toupper() -- returns uppercased copy
// =============================================================================

TEST(StringMethods, Toupper) {
  StringFixture f;
  f.CreateStringVar("s", "hello");
  auto* call = f.MakeMethodCall("s", "toupper");
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(VecToString(result), "HELLO");
}

// =============================================================================
// §6.16.5: tolower() -- returns lowercased copy
// =============================================================================

TEST(StringMethods, Tolower) {
  StringFixture f;
  f.CreateStringVar("s", "HELLO");
  auto* call = f.MakeMethodCall("s", "tolower");
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(VecToString(result), "hello");
}

// =============================================================================
// §6.16.6: compare(s) -- lexicographic compare
// =============================================================================

TEST(StringMethods, CompareEqual) {
  StringFixture f;
  f.CreateStringVar("s", "abc");
  f.CreateStringVar("t", "abc");
  // Build: s.compare(t) where t is passed as identifier
  auto* arg = f.arena.Create<Expr>();
  arg->kind = ExprKind::kIdentifier;
  arg->text = "t";
  auto* call = f.MakeMethodCall("s", "compare", {arg});
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(static_cast<int64_t>(result.ToUint64()), 0);
}

TEST(StringMethods, CompareLessThan) {
  StringFixture f;
  f.CreateStringVar("s", "abc");
  f.CreateStringVar("t", "abd");
  auto* arg = f.arena.Create<Expr>();
  arg->kind = ExprKind::kIdentifier;
  arg->text = "t";
  auto* call = f.MakeMethodCall("s", "compare", {arg});
  auto result = EvalExpr(call, f.ctx, f.arena);
  // compare returns negative when s < t
  auto signed_val = static_cast<int32_t>(result.ToUint64() & 0xFFFFFFFF);
  EXPECT_LT(signed_val, 0);
}

// =============================================================================
// §6.16.7: icompare(s) -- case-insensitive compare
// =============================================================================

TEST(StringMethods, IcompareEqual) {
  StringFixture f;
  f.CreateStringVar("s", "Hello");
  f.CreateStringVar("t", "hello");
  auto* arg = f.arena.Create<Expr>();
  arg->kind = ExprKind::kIdentifier;
  arg->text = "t";
  auto* call = f.MakeMethodCall("s", "icompare", {arg});
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(static_cast<int64_t>(result.ToUint64()), 0);
}

// =============================================================================
// §6.16.8: substr(i, j) -- extract substring from index i to j
// =============================================================================

TEST(StringMethods, Substr) {
  StringFixture f;
  f.CreateStringVar("s", "hello world");
  auto* call = f.MakeMethodCall("s", "substr",
                                {f.MakeIntLiteral(6), f.MakeIntLiteral(10)});
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(VecToString(result), "world");
}

// =============================================================================
// §6.16.9: atoi() / atohex() / atooct() / atobin()
// =============================================================================

TEST(StringMethods, Atoi) {
  StringFixture f;
  f.CreateStringVar("s", "42");
  auto* call = f.MakeMethodCall("s", "atoi");
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 42u);
}

TEST(StringMethods, Atohex) {
  StringFixture f;
  f.CreateStringVar("s", "1f");
  auto* call = f.MakeMethodCall("s", "atohex");
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0x1fu);
}

TEST(StringMethods, Atooct) {
  StringFixture f;
  f.CreateStringVar("s", "77");
  auto* call = f.MakeMethodCall("s", "atooct");
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 077u);
}

TEST(StringMethods, Atobin) {
  StringFixture f;
  f.CreateStringVar("s", "1010");
  auto* call = f.MakeMethodCall("s", "atobin");
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0b1010u);
}

// =============================================================================
// §6.16.10: atoreal() -- convert string to real
// =============================================================================

TEST(StringMethods, Atoreal) {
  StringFixture f;
  f.CreateStringVar("s", "3.14");
  auto* call = f.MakeMethodCall("s", "atoreal");
  auto result = EvalExpr(call, f.ctx, f.arena);
  uint64_t bits = result.ToUint64();
  double d = 0.0;
  std::memcpy(&d, &bits, sizeof(double));
  EXPECT_NEAR(d, 3.14, 0.001);
}

// =============================================================================
// §6.16.11: itoa(i) -- assign decimal string representation to variable
// =============================================================================

TEST(StringMethods, Itoa) {
  StringFixture f;
  auto* var = f.CreateStringVar("s", "");
  auto* call = f.MakeMethodCall("s", "itoa", {f.MakeIntLiteral(123)});
  EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(VecToString(var->value), "123");
}

// =============================================================================
// §6.16.12: hextoa(i) -- assign hex string representation to variable
// =============================================================================

TEST(StringMethods, Hextoa) {
  StringFixture f;
  auto* var = f.CreateStringVar("s", "");
  auto* call = f.MakeMethodCall("s", "hextoa", {f.MakeIntLiteral(255)});
  EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(VecToString(var->value), "ff");
}

// =============================================================================
// §6.16.13: octtoa(i) -- assign octal string representation to variable
// =============================================================================

TEST(StringMethods, Octtoa) {
  StringFixture f;
  auto* var = f.CreateStringVar("s", "");
  auto* call = f.MakeMethodCall("s", "octtoa", {f.MakeIntLiteral(8)});
  EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(VecToString(var->value), "10");
}

// =============================================================================
// §6.16.14: bintoa(i) -- assign binary string representation to variable
// =============================================================================

TEST(StringMethods, Bintoa) {
  StringFixture f;
  auto* var = f.CreateStringVar("s", "");
  auto* call = f.MakeMethodCall("s", "bintoa", {f.MakeIntLiteral(10)});
  EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(VecToString(var->value), "1010");
}

// =============================================================================
// §6.16.15: realtoa(r) -- assign real string representation to variable
// =============================================================================

TEST(StringMethods, Realtoa) {
  StringFixture f;
  auto* var = f.CreateStringVar("s", "");
  // Encode 2.5 as real (double) bits in an integer literal.
  double d = 2.5;
  uint64_t bits = 0;
  std::memcpy(&bits, &d, sizeof(double));
  auto* call = f.MakeMethodCall("s", "realtoa", {f.MakeIntLiteral(bits)});
  EvalExpr(call, f.ctx, f.arena);
  std::string result = VecToString(var->value);
  EXPECT_FALSE(result.empty());
  // The string should represent 2.5 in some decimal form.
  EXPECT_NE(result.find("2.5"), std::string::npos);
}
