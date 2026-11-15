#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

const char* const kRhs =
    "cannot be called on the right-hand side of a checker variable assignment";
const char* const kContinuous = "cannot be called in a continuous assignment";

std::vector<uint32_t> AssignmentsTo(const std::string& src,
                                    std::string_view marker) {
  std::vector<uint32_t> lines;
  uint32_t line = 1;
  size_t start = 0;
  while (start < src.size()) {
    size_t end = src.find('\n', start);
    if (end == std::string::npos) end = src.size();
    std::string_view text(src.data() + start, end - start);
    if (text.find(marker) != std::string_view::npos &&
        text.find('=') != std::string_view::npos) {
      lines.push_back(line);
    }
    ++line;
    start = end + 1;
  }
  return lines;
}

void ExpectRhsCalls(const std::string& src) {
  ElabFixture f;
  ElaborateSrc(src, f, "top");
  const auto& diags = f.diag.Diagnostics();
  for (uint32_t line : AssignmentsTo(src, "x_bad")) {
    EXPECT_TRUE(ReportedError(diags, kRhs, line, "17.8") ||
                ReportedError(diags, kContinuous, line, "13.4"))
        << line;
  }
  for (uint32_t line : AssignmentsTo(src, "y_ok")) {
    EXPECT_FALSE(ReportedError(diags, kRhs, line, "17.8")) << line;
  }
}

std::string InTop(const std::string& cu, const std::string& items,
                  const char* type = "bit") {
  std::string src = cu;
  src += "checker chk(logic clk, en, ";
  src += type;
  src += " a);\n";
  src += items;
  src +=
      "endchecker\n"
      "module top;\n"
      "  logic clk, en;\n  ";
  src += type;
  src +=
      " a;\n"
      "  chk c(clk, en, a);\n"
      "endmodule\n";
  return src;
}

const char* const kWriters =
    "  bit t, q;\n"
    "  function automatic bit fo(input bit x, output bit o);\n"
    "    o = x;\n"
    "    return x;\n"
    "  endfunction\n"
    "  function automatic bit fi(inout bit io);\n"
    "    return io;\n"
    "  endfunction\n"
    "  function automatic bit fr(ref bit r);\n"
    "    return r;\n"
    "  endfunction\n"
    "  function automatic bit fc(input bit x, const ref bit c);\n"
    "    return x & c;\n"
    "  endfunction\n";

TEST(CheckerWritingArgumentCalls, ACheckerLocalFunctionInEachAssignment) {
  ExpectRhsCalls(
      InTop("", std::string(kWriters) +
                    "  bit x_bad1, x_bad2, x_bad3, x_bad4, x_bad5, "
                    "x_bad6, x_bad7, x_bad8, x_bad9;\n"
                    "  bit y_ok1, y_ok2;\n"
                    "  rand bit x_bad10;\n"
                    "  always_latch if (en) x_bad1 = fo(a, t);\n"
                    "  always_latch if (en) x_bad2 = fi(t);\n"
                    "  always_latch if (en) x_bad3 = fr(q);\n"
                    "  assign x_bad4 = fo(a, t);\n"
                    "  assign x_bad5 = fi(t);\n"
                    "  assign x_bad6 = fr(q);\n"
                    "  assign y_ok1 = fc(a, q);\n"
                    "  always_ff @(posedge clk)\n"
                    "    if (en) begin\n"
                    "      x_bad7 <= fo(a, t);\n"
                    "    end\n"
                    "  always_ff @(posedge clk) x_bad8 <= en ? "
                    "fi(t) : 1'b0;\n"
                    "  always_comb x_bad9 = en ? 1'b0 : fr(q);\n"
                    "  always_ff @(posedge clk) x_bad10 <= fo(a, "
                    "t);\n"
                    "  always_ff @(posedge clk) y_ok2 <= fc(a, q);\n"));
}

TEST(CheckerWritingArgumentCalls, AnEnclosingScopesFunctionInAProcedure) {
  const std::string kModuleFunctions =
      "  function automatic bit mi(inout bit io);\n"
      "    return io;\n"
      "  endfunction\n"
      "  function automatic bit mr(ref bit r);\n"
      "    return r;\n"
      "  endfunction\n"
      "  function automatic bit mc(input bit x, const ref bit c);\n"
      "    return x & c;\n"
      "  endfunction\n"
      "  function automatic bit mo(input bit x, output bit o);\n"
      "    o = x;\n"
      "    return x;\n"
      "  endfunction\n";
  const std::string kUser =
      "  checker inner(logic clk, bit a);\n"
      "    bit t, x_bad;\n"
      "    always_ff @(posedge clk) x_bad <= mo(a, t);\n"
      "  endchecker\n";
  std::string src = "module top;\n";
  src += kModuleFunctions;
  src +=
      "  checker c(logic clk, bit a);\n"
      "    bit t, q, x_bad1, x_bad2, y_ok;\n"
      "    always_ff @(posedge clk) x_bad1 <= mi(t);\n"
      "    always_ff @(posedge clk) x_bad2 <= mr(q);\n"
      "    always_ff @(posedge clk) y_ok <= mc(a, q);\n"
      "  endchecker\n"
      "  logic clk;\n"
      "  bit a;\n"
      "  c u(clk, a);\n"
      "  ifc i(clk, a);\n"
      "  prg p(clk, a);\n"
      "  outer o(clk, a);\n"
      "endmodule\n"
      "interface ifc(input logic clk, input bit a);\n";
  src += kModuleFunctions;
  src += kUser;
  src += "  inner n(clk, a);\nendinterface\nprogram prg(input logic clk, ";
  src += "input bit a);\n";
  src += kModuleFunctions;
  src += kUser;
  src += "  inner n(clk, a);\nendprogram\nchecker outer(logic clk, bit a);\n";
  src += kModuleFunctions;
  src += kUser;
  src += "  inner n(clk, a);\nendchecker\n";
  ExpectRhsCalls(src);
}

TEST(CheckerWritingArgumentCalls,
     DISABLED_AnEnclosingModulesFunctionInAContinuousAssignment) {
  ExpectRhsCalls(
      "module top;\n"
      "  function automatic bit mo(input bit x, output bit o);\n"
      "    o = x;\n"
      "    return x;\n"
      "  endfunction\n"
      "  function automatic bit mi(inout bit io);\n"
      "    return io;\n"
      "  endfunction\n"
      "  function automatic bit mr(ref bit r);\n"
      "    return r;\n"
      "  endfunction\n"
      "  checker c(bit a);\n"
      "    bit t, q, x_bad1, x_bad2, x_bad3;\n"
      "    assign x_bad1 = mo(a, t);\n"
      "    assign x_bad2 = mi(t);\n"
      "    assign x_bad3 = mr(q);\n"
      "  endchecker\n"
      "  bit a;\n"
      "  c u(a);\n"
      "endmodule\n");
}

const char* const kPackageWriters =
    "package pk;\n"
    "  function automatic bit po(input bit x, output bit o);\n"
    "    o = x;\n"
    "    return x;\n"
    "  endfunction\n"
    "  function automatic bit pc(input bit x, const ref bit c);\n"
    "    return x & c;\n"
    "  endfunction\n"
    "  function automatic bit pn(input bit x);\n"
    "    return x;\n"
    "  endfunction\n"
    "  checker pchk(logic clk, bit a);\n"
    "    bit t, q, x_bad, y_ok1, y_ok2;\n"
    "    always_ff @(posedge clk) x_bad <= po(a, t);\n"
    "    always_ff @(posedge clk) y_ok1 <= pc(a, q);\n"
    "    always_ff @(posedge clk) y_ok2 <= pn(a);\n"
    "  endchecker\n"
    "endpackage\n"
    "function automatic bit uo(input bit x, output bit o);\n"
    "  o = x;\n"
    "  return x;\n"
    "endfunction\n"
    "function automatic bit ur(ref bit r);\n"
    "  return r;\n"
    "endfunction\n"
    "class K;\n"
    "  static function bit ko(input bit x, output bit o);\n"
    "    o = x;\n"
    "    return x;\n"
    "  endfunction\n"
    "  static function bit kn(input bit x);\n"
    "    return x;\n"
    "  endfunction\n"
    "endclass\n"
    "import pk::*;\n";

TEST(CheckerWritingArgumentCalls,
     DISABLED_AFunctionDeclaredElsewhereIsChecked) {
  const std::string kSrc = InTop(
      kPackageWriters,
      "  bit t, q;\n"
      "  bit x_bad1, x_bad2, x_bad3, x_bad4, x_bad5, x_bad6, x_bad7, x_bad8;\n"
      "  bit y_ok1, y_ok2, y_ok3, y_ok4;\n"
      "  always_ff @(posedge clk) x_bad1 <= pk::po(a, t);\n"
      "  always_ff @(posedge clk) x_bad2 <= po(a, t);\n"
      "  always_ff @(posedge clk) x_bad3 <= uo(a, t);\n"
      "  always_ff @(posedge clk) x_bad4 <= $unit::ur(q);\n"
      "  always_ff @(posedge clk) x_bad5 <= K::ko(a, t);\n"
      "  assign x_bad6 = pk::po(a, t);\n"
      "  always_ff @(posedge clk) y_ok1 <= pk::pc(a, q);\n"
      "  always_ff @(posedge clk) y_ok2 <= pn(a);\n"
      "  always_ff @(posedge clk) y_ok3 <= K::kn(a);\n"
      "  if (1) begin : g\n"
      "    function automatic bit go(input bit x, output bit o);\n"
      "      o = x;\n"
      "      return x;\n"
      "    endfunction\n"
      "    function automatic bit gn(input bit x);\n"
      "      return x;\n"
      "    endfunction\n"
      "    always_ff @(posedge clk) x_bad7 <= go(a, t);\n"
      "    assign x_bad8 = go(a, q);\n"
      "    always_ff @(posedge clk) y_ok4 <= gn(a);\n"
      "  end\n"
      "  pk::pchk pi(clk, a);\n");
  ExpectRhsCalls(kSrc);
}

const char* const kStateful =
    "package pk;\n"
    "  int pv;\n"
    "endpackage\n"
    "int uv;\n";

TEST(CheckerStatefulCalls, ACheckerLocalSideEffectInEachForm) {
  ExpectRhsCalls(InTop(
      kStateful,
      "  int count, arr [2];\n"
      "  int x_bad1, x_bad2, x_bad3, x_bad4, x_bad5, x_bad6, x_bad7, x_bad8;\n"
      "  int x_bad9, x_bad10, y_ok2;\n"
      "  function int bump(int x);\n"
      "    count = x;\n"
      "    return x;\n"
      "  endfunction\n"
      "  function automatic int abump(int x);\n"
      "    count = x;\n"
      "    return x;\n"
      "  endfunction\n"
      "  function int addto(int x);\n"
      "    count += x;\n"
      "    return x;\n"
      "  endfunction\n"
      "  function int toarr(int x);\n"
      "    arr[0] = x;\n"
      "    return x;\n"
      "  endfunction\n"
      "  function int topk(int x);\n"
      "    pk::pv = x;\n"
      "    return x;\n"
      "  endfunction\n"
      "  function int tounit(int x);\n"
      "    $unit::uv = x;\n"
      "    return x;\n"
      "  endfunction\n"
      "  function int kept(int x);\n"
      "    static int k = 0;\n"
      "    k = k + x;\n"
      "    return k;\n"
      "  endfunction\n"
      "  function int fresh(int x);\n"
      "    int k;\n"
      "    k = x;\n"
      "    return k;\n"
      "  endfunction\n"
      "  always_comb x_bad1 = bump(a);\n"
      "  always_latch if (en) x_bad2 = bump(a);\n"
      "  always_ff @(posedge clk) x_bad3 <= abump(a);\n"
      "  always_ff @(posedge clk)\n"
      "    if (en) begin\n"
      "      x_bad4 <= bump(a);\n"
      "    end\n"
      "  always_ff @(posedge clk) x_bad5 <= en ? bump(a) : 0;\n"
      "  always_ff @(posedge clk) x_bad6 <= addto(a);\n"
      "  always_ff @(posedge clk) x_bad7 <= toarr(a);\n"
      "  always_ff @(posedge clk) x_bad8 <= topk(a);\n"
      "  always_ff @(posedge clk) x_bad9 <= tounit(a);\n"
      "  always_ff @(posedge clk) x_bad10 <= kept(a);\n"
      "  always_ff @(posedge clk) y_ok2 <= fresh(a);\n",
      "int"));
}

TEST(CheckerStatefulCalls, AnEnclosingScopesSideEffectIsReported) {
  const std::string kBump =
      "  int count;\n"
      "  function int bump(int x);\n"
      "    count = x;\n"
      "    return x;\n"
      "  endfunction\n"
      "  checker inner(logic clk, int a);\n"
      "    int x_bad;\n"
      "    always_ff @(posedge clk) x_bad <= bump(a);\n"
      "  endchecker\n"
      "  inner n(clk, a);\n";
  std::string src =
      "module top;\n"
      "  logic clk;\n"
      "  int a;\n"
      "  ifc i(clk, a);\n"
      "  prg p(clk, a);\n"
      "  outer o(clk, a);\n"
      "endmodule\n"
      "interface ifc(input logic clk, input int a);\n";
  src += kBump;
  src += "endinterface\nprogram prg(input logic clk, input int a);\n";
  src += kBump;
  src += "endprogram\nchecker outer(logic clk, int a);\n";
  src += kBump;
  src += "endchecker\n";
  ExpectRhsCalls(src);
}

TEST(CheckerStatefulCalls,
     DISABLED_AStateOrSideEffectTheCheckMissesIsReported) {
  ExpectRhsCalls(InTop("",
                       "  int count;\n"
                       "  int x_bad1, x_bad2, x_bad3, x_bad4, x_bad5, x_bad6;\n"
                       "  function int inc(int x);\n"
                       "    count++;\n"
                       "    return x;\n"
                       "  endfunction\n"
                       "  function int dec(int x);\n"
                       "    --count;\n"
                       "    return x;\n"
                       "  endfunction\n"
                       "  function int bump(int x);\n"
                       "    count = x;\n"
                       "    return x;\n"
                       "  endfunction\n"
                       "  function int skept(int x);\n"
                       "    static int k;\n"
                       "    k = k + x;\n"
                       "    return k;\n"
                       "  endfunction\n"
                       "  function int ikept(int x);\n"
                       "    int k;\n"
                       "    k = k + x;\n"
                       "    return k;\n"
                       "  endfunction\n"
                       "  function automatic int outer_call(int x);\n"
                       "    return bump(x);\n"
                       "  endfunction\n"
                       "  always_ff @(posedge clk) x_bad1 <= inc(a);\n"
                       "  always_ff @(posedge clk) x_bad2 <= dec(a);\n"
                       "  assign x_bad3 = bump(a);\n"
                       "  always_ff @(posedge clk) x_bad4 <= skept(a);\n"
                       "  always_ff @(posedge clk) x_bad5 <= ikept(a);\n"
                       "  always_ff @(posedge clk) x_bad6 <= outer_call(a);\n",
                       "int"));
}

const char* const kElsewhere =
    "package pk;\n"
    "  int pv;\n"
    "  function int pbump(int x);\n"
    "    pv = x;\n"
    "    return x;\n"
    "  endfunction\n"
    "  function automatic int ppure(int x);\n"
    "    return x + 1;\n"
    "  endfunction\n"
    "  checker pchk(logic clk, int a);\n"
    "    int x_bad, y_ok;\n"
    "    always_ff @(posedge clk) x_bad <= pbump(a);\n"
    "    always_ff @(posedge clk) y_ok <= ppure(a);\n"
    "  endchecker\n"
    "endpackage\n"
    "int uv;\n"
    "function int ubump(int x);\n"
    "  uv = x;\n"
    "  return x;\n"
    "endfunction\n"
    "function automatic int upure(int x);\n"
    "  return x + 1;\n"
    "endfunction\n"
    "class C;\n"
    "  static int cv;\n"
    "  static function int cbump(int x);\n"
    "    cv = x;\n"
    "    return x;\n"
    "  endfunction\n"
    "  static function int cpure(int x);\n"
    "    return x + 1;\n"
    "  endfunction\n"
    "endclass\n"
    "import pk::*;\n";

TEST(CheckerStatefulCalls, DISABLED_ASideEffectDeclaredElsewhereIsReported) {
  ExpectRhsCalls(InTop(kElsewhere,
                       "  int x_bad1, x_bad2, x_bad3, x_bad4, x_bad5;\n"
                       "  int y_ok1, y_ok2, y_ok3, y_ok4;\n"
                       "  always_ff @(posedge clk) x_bad1 <= pk::pbump(a);\n"
                       "  always_ff @(posedge clk) x_bad2 <= pbump(a);\n"
                       "  always_ff @(posedge clk) x_bad3 <= ubump(a);\n"
                       "  always_ff @(posedge clk) x_bad4 <= C::cbump(a);\n"
                       "  always_ff @(posedge clk) y_ok1 <= pk::ppure(a);\n"
                       "  always_ff @(posedge clk) y_ok2 <= upure(a);\n"
                       "  always_ff @(posedge clk) y_ok3 <= C::cpure(a);\n"
                       "  if (1) begin : g\n"
                       "    int gc;\n"
                       "    function int gbump(int x);\n"
                       "      gc = x;\n"
                       "      return x;\n"
                       "    endfunction\n"
                       "    always_ff @(posedge clk) x_bad5 <= gbump(a);\n"
                       "    always_ff @(posedge clk) y_ok4 <= upure(a);\n"
                       "  end\n"
                       "  pk::pchk pi(clk, a);\n",
                       "int"));
}

TEST(CheckerStatefulCalls,
     DISABLED_AnAutomaticLocalOfAStaticFunctionIsAccepted) {
  ExpectRhsCalls(InTop("",
                       "  int y_ok1, y_ok2;\n"
                       "  function int scratch(int x);\n"
                       "    automatic int s = x;\n"
                       "    return s + 1;\n"
                       "  endfunction\n"
                       "  function int later(int x);\n"
                       "    automatic int s;\n"
                       "    s = x;\n"
                       "    return s + 1;\n"
                       "  endfunction\n"
                       "  always_ff @(posedge clk) y_ok1 <= scratch(a);\n"
                       "  always_ff @(posedge clk) y_ok2 <= later(a);\n",
                       "int"));
}

}  // namespace
