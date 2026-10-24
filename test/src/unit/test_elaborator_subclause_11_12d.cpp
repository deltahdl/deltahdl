#include <gtest/gtest.h>

#include <cstdint>
#include <format>
#include <string>
#include <string_view>

#include "common/types.h"
#include "elaborator/elaborator.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "lexer/lexer.h"
#include "parser/ast_design.h"
#include "parser/parser.h"

using namespace delta;

namespace {

constexpr std::string_view kNotCastCompatible =
    "is not cast compatible with the type of formal";

// §8.13 with §8.23: a class inherits the members of the class it extends, so
// `E::t` is C's array of two ints, and E's own `et`, written with `t`, is the
// same type, as is the typedef of a class nested in E. A class behind its
// package's name is extended too, and §8.26.2 has an interface class inherit
// the types of every interface class it extends. Each array is reported for
// three ints, and three bytes for an int.
TEST(LetActualClassScopeElaboration, ATypeADerivedClassInheritsIsFollowed) {
  ElabFixture f;
  ElaborateSrc(
      "class C;\n"
      "  typedef int t [2];\n"
      "endclass\n"
      "package p;\n"
      "  class B;\n"
      "    typedef byte b_t [3];\n"
      "  endclass\n"
      "endpackage\n"
      "class E extends C;\n"
      "  typedef t et;\n"
      "  class EN;\n"
      "    typedef int e_t [2];\n"
      "  endclass\n"
      "endclass\n"
      "class F extends p::B;\n"
      "endclass\n"
      "interface class I1;\n"
      "  typedef int i1_t [2];\n"
      "endclass\n"
      "interface class I2;\n"
      "  typedef int i2_t [2];\n"
      "endclass\n"
      "interface class I3 extends I1, I2;\n"
      "endclass\n"
      "module m;\n"
      "  let h(int x [3]) = x[0];\n"
      "  let n(int x) = x;\n"
      "  E::t a; E::et b; E::EN::e_t c; F::b_t d; I3::i1_t e; I3::i2_t g;\n"
      "  initial $display(\"%0d\", h(a));\n"
      "  initial $display(\"%0d\", h(b));\n"
      "  initial $display(\"%0d\", h(c));\n"
      "  initial $display(\"%0d\", n(d));\n"
      "  initial $display(\"%0d\", h(e));\n"
      "  initial $display(\"%0d\", h(g));\n"
      "endmodule\n",
      f);
  for (uint32_t line : {29u, 30u, 31u, 32u, 33u, 34u}) {
    EXPECT_TRUE(
        ReportedError(f.diag.Diagnostics(), kNotCastCompatible, line, "11.12"))
        << line;
  }
}

// §8.13 with §8.25: the class a class extends is a class_type (A.2.2.1),
// which a typedef naming the class may stand for, and which may be a class
// nested in another, written behind that class's name. Either way it is
// followed, so `G::t`, C's array of two ints, and `H::i_t`, Inner's, are
// each reported for three ints.
TEST(LetActualClassScopeElaboration, ABaseThroughATypedefOrAClassIsFollowed) {
  ElabFixture f;
  ElaborateSrc(
      "class C;\n"
      "  typedef int t [2];\n"
      "endclass\n"
      "typedef C c_t;\n"
      "class G extends c_t;\n"
      "endclass\n"
      "class Outer;\n"
      "  class Inner;\n"
      "    typedef int i_t [2];\n"
      "  endclass\n"
      "endclass\n"
      "class H extends Outer::Inner;\n"
      "endclass\n"
      "module m;\n"
      "  let h(int x [3]) = x[0];\n"
      "  G::t k; H::i_t l;\n"
      "  initial $display(\"%0d\", h(k));\n"
      "  initial $display(\"%0d\", h(l));\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kNotCastCompatible, 17, "11.12"));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kNotCastCompatible, 18, "11.12"));
}

// §8.13: a base written through a chain of typedef names, 31 long here, is
// followed to its class; one of 32, which may run through a name twice, is
// not, nor is a base nothing declares. A class whose base is not found has
// no frame, so the calls passing what it declares or inherits are left
// unjudged.
TEST(LetActualClassScopeElaboration, ABaseIsFollowedThroughTypedefsToABound) {
  std::string src = "class C;\n  typedef int t [2];\nendclass\ntypedef C c0;\n";
  for (int i = 1; i < 32; ++i)
    src += std::format("typedef c{} c{};\n", i - 1, i);
  src +=
      "class G extends c30;\n"
      "endclass\n"
      "class H extends c31;\n"
      "endclass\n"
      "class J extends Missing;\n"
      "  typedef int j_t [2];\n"
      "endclass\n"
      "module m;\n"
      "  let h(int x [3]) = x[0];\n"
      "  G::t k; H::t l; J::j_t n;\n"
      "  initial $display(\"%0d\", h(k));\n"
      "  initial $display(\"%0d\", h(l) + h(n));\n"
      "endmodule\n";
  ElabFixture f;
  ElaborateSrc(src, f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kNotCastCompatible, 46, "11.12"));
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), kNotCastCompatible, 47, "11.12"));
}

// §8.25.1: `P#()::ks_t` is the typedef of P's default specialization, a
// structure of one 16-bit member, and `P#(4)::ks_t` that of P#(4), of one
// 32-bit member, so an int is reported for the first and fits the second by
// bit-stream cast (§6.24.3). A name a specialization's typedef stands for is
// looked up where it was written: `ut` and `N`, written in P, in P, where
// `N` is P's nested class and `ut` the compilation unit's int; `T`'s default
// int in P's header; and the `N` the argument of `P#(2, N)` gives T at the
// call, m's class. So an array of three ints is no `pt` or `tt`, an int no
// handle, and m's N no handle of P's N, which is no class related to it.
TEST(LetActualClassScopeElaboration, ATypeOfASpecializationIsJudged) {
  ElabFixture f;
  ElaborateSrc(
      "typedef int ut;\n"
      "class P #(int K = 2, type T = int);\n"
      "  typedef struct { logic [K*8-1:0] a; } ks_t;\n"
      "  typedef ut pt;\n"
      "  typedef T tt;\n"
      "  class N;\n"
      "  endclass\n"
      "  typedef N nt;\n"
      "endclass\n"
      "module m;\n"
      "  class N;\n"
      "  endclass\n"
      "  let z(P#()::ks_t x) = x.a;\n"
      "  let z4(P#(4)::ks_t x) = x.a;\n"
      "  let zp(P#()::pt x) = x;\n"
      "  let zt(P#()::tt x) = x;\n"
      "  let zd(P#(2, N)::tt x) = x;\n"
      "  let zn(P#()::nt x) = x;\n"
      "  int i; int a3 [3]; N nh;\n"
      "  initial $display(\"%0d\", z(i));\n"
      "  initial $display(\"%0d\", z4(i));\n"
      "  initial $display(\"%0d\", zp(a3));\n"
      "  initial $display(\"%0d\", zt(a3));\n"
      "  initial $display(\"%0d\", zd(i));\n"
      "  initial $display(\"%0d\", zd(nh));\n"
      "  initial $display(\"%0d\", zn(i));\n"
      "  initial $display(\"%0d\", zn(nh));\n"
      "endmodule\n",
      f);
  for (uint32_t line : {20u, 22u, 23u, 24u, 26u, 27u}) {
    EXPECT_TRUE(
        ReportedError(f.diag.Diagnostics(), kNotCastCompatible, line, "11.12"))
        << line;
  }
  for (uint32_t line : {21u, 25u}) {
    EXPECT_FALSE(
        ReportedError(f.diag.Diagnostics(), kNotCastCompatible, line, "11.12"))
        << line;
  }
}

// §8.25.1: a name written in a class with parameters is looked up in the
// class, which a variable of the class's name hides where the
// specialization is written, so there the prefix names no class and the
// type `pt` stands for is left unjudged.
TEST(LetActualClassScopeElaboration, ASpecializationOfAHiddenClassIsUnjudged) {
  ElabFixture f;
  ElaborateSrc(
      "typedef int ut;\n"
      "class P #(int K = 2);\n"
      "  typedef ut pt;\n"
      "endclass\n"
      "module m;\n"
      "  int P;\n"
      "  let zp(P#()::pt x) = x;\n"
      "  int a3 [3];\n"
      "  initial $display(\"%0d\", zp(a3));\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), kNotCastCompatible, 9, "11.12"));
}

// §6.7.1: a net declared with no data type, or with only a range, is of the
// implicit type logic: `d`, of one bit, fits an int formal, and `v`, of 64
// bits, an array of two ints by bit-stream cast (§6.24.3), while `v8`, of 8
// bits, fits no such array.
TEST(LetActualNetTypeElaboration, ANetDeclaredWithNoDataTypeIsLogic) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire d;\n"
      "  wire [63:0] v;\n"
      "  tri [7:0] v8;\n"
      "  let n(int x) = x;\n"
      "  let f(int x [2]) = x[0];\n"
      "  initial $display(\"%0d\", n(d) + f(v));\n"
      "  initial $display(\"%0d\", f(v8));\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), kNotCastCompatible, 7, "11.12"));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kNotCastCompatible, 8, "11.12"));
}

// §6.10: a name a continuous assignment's target, a primitive's or a UDP's
// terminal list, an instance's port connections or an alias writes alone, and
// that nothing declares, is an implicit scalar net, a 1-bit logic, which no
// array of two ints takes; an int formal takes it. A terminal naming the
// declared net `d`, a literal terminal and an empty port connection declare
// nothing.
TEST(LetActualImplicitNetElaboration, AnImplicitNetIsJudgedAsAScalar) {
  ElabFixture f;
  ElaborateSrc(
      "primitive buf1 (output o, input i);\n"
      "  table\n"
      "    0 : 0;\n"
      "    1 : 1;\n"
      "  endtable\n"
      "endprimitive\n"
      "module child (input logic a, output logic y, output logic z);\n"
      "  assign y = a;\n"
      "  assign z = a;\n"
      "endmodule\n"
      "module m;\n"
      "  wire d;\n"
      "  assign {w, w2} = 2'b11;\n"
      "  and g1 (gy, w, 1'b1);\n"
      "  buf1 u1 (uy, d);\n"
      "  child c (.a(w), .y(cy), .z());\n"
      "  alias al = al2;\n"
      "  let f(int x [2]) = x[0];\n"
      "  let n(int x) = x;\n"
      "  initial $display(\"%0d\", f(w));\n"
      "  initial $display(\"%0d\", f(w2));\n"
      "  initial $display(\"%0d\", f(gy));\n"
      "  initial $display(\"%0d\", f(uy));\n"
      "  initial $display(\"%0d\", f(cy));\n"
      "  initial $display(\"%0d\", f(al));\n"
      "  initial $display(\"%0d\", n(w));\n"
      "endmodule\n",
      f, "m");
  for (uint32_t line : {20u, 21u, 22u, 23u, 24u, 25u}) {
    EXPECT_TRUE(
        ReportedError(f.diag.Diagnostics(), kNotCastCompatible, line, "11.12"))
        << line;
  }
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), kNotCastCompatible, 26, "11.12"));
}

// §22.8: under `default_nettype none no implicit net is assumed, so the
// target of the continuous assignment is an error and declares nothing, and
// the call passing it is left to that report.
TEST(LetActualImplicitNetElaboration, NoImplicitNetUnderDefaultNettypeNone) {
  ElabFixture f;
  auto fid = f.mgr.AddFile("<test>",
                           "module m;\n"
                           "  assign w = 1'b1;\n"
                           "  let f(int x [2]) = x[0];\n"
                           "  initial $display(\"%0d\", f(w));\n"
                           "endmodule\n");
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  CompilationUnit* cu = parser.Parse();
  cu->default_nettype = NetType::kNone;
  Elaborator elab(f.arena, f.diag, cu);
  elab.Elaborate("m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "implicit net 'w' forbidden by", 2, "22.8"));
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), kNotCastCompatible, 4, "11.12"));
}

}  // namespace
