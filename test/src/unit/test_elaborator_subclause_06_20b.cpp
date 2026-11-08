#include <gtest/gtest.h>

#include <cstdint>
#include <span>
#include <string>

#include "fixture_elaborator.h"
#include "helpers_elab_no_error.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

struct BuiltInWrite {
  const char* call;
  const char* message;
};

void ExpectEachWriteReported(const char* prelude, uint32_t line,
                             std::span<const BuiltInWrite> writes) {
  for (const BuiltInWrite& write : writes) {
    SCOPED_TRACE(write.call);
    ElabFixture f;
    ElaborateSrc(std::string(prelude) + write.call + ";\nendmodule\n", f);
    EXPECT_TRUE(
        ReportedError(f.diag.Diagnostics(), write.message, line, "6.20"));
  }
}

TEST(ConstAssignElaboration,
     ASystemCallReportsAConstantInEveryArgumentItWrites) {
  const BuiltInWrite kWrites[] = {
      {"$swrite(P, \"%d\", i)", "constant 'P' cannot be written by '$swrite'"},
      {"$swriteb(P, i)", "constant 'P' cannot be written by '$swriteb'"},
      {"$swriteh(P, i)", "constant 'P' cannot be written by '$swriteh'"},
      {"$swriteo(P, i)", "constant 'P' cannot be written by '$swriteo'"},
      {"$sformat(P, \"%d\", i)",
       "constant 'P' cannot be written by '$sformat'"},
      {"i = $fgets(P, fd)", "constant 'P' cannot be written by '$fgets'"},
      {"i = $fscanf(fd, \"%d %d\", i, P)",
       "constant 'P' cannot be written by '$fscanf'"},
      {"i = $sscanf(s, \"%d %d\", i, P)",
       "constant 'P' cannot be written by '$sscanf'"},
      {"i = $fread(P, fd)", "constant 'P' cannot be written by '$fread'"},
      {"i = $ferror(fd, P)", "constant 'P' cannot be written by '$ferror'"},
      {"$readmemb(\"m.txt\", P)",
       "constant 'P' cannot be written by '$readmemb'"},
      {"$readmemh(\"m.txt\", P)",
       "constant 'P' cannot be written by '$readmemh'"},
      {"i = $value$plusargs(\"n=%d\", P)",
       "constant 'P' cannot be written by '$value$plusargs'"},
      {"$cast(P, i)", "constant 'P' cannot be written by '$cast'"},
      {"i = $cast(P, i)", "constant 'P' cannot be written by '$cast'"},
      {"i = $random(P)", "constant 'P' cannot be written by '$random'"},
      {"i = $dist_uniform(P, 0, 9)",
       "constant 'P' cannot be written by '$dist_uniform'"},
      {"i = $dist_normal(P, 0, 1)",
       "constant 'P' cannot be written by '$dist_normal'"},
      {"i = $dist_exponential(P, 1)",
       "constant 'P' cannot be written by '$dist_exponential'"},
      {"i = $dist_poisson(P, 1)",
       "constant 'P' cannot be written by '$dist_poisson'"},
      {"i = $dist_chi_square(P, 1)",
       "constant 'P' cannot be written by '$dist_chi_square'"},
      {"i = $dist_t(P, 1)", "constant 'P' cannot be written by '$dist_t'"},
      {"i = $dist_erlang(P, 1, 1)",
       "constant 'P' cannot be written by '$dist_erlang'"},
      {"$q_initialize(1, 1, 8, P)",
       "constant 'P' cannot be written by '$q_initialize'"},
      {"$q_add(1, 1, 1, P)", "constant 'P' cannot be written by '$q_add'"},
      {"$q_remove(1, P, i, i)",
       "constant 'P' cannot be written by '$q_remove'"},
      {"$q_remove(1, i, P, i)",
       "constant 'P' cannot be written by '$q_remove'"},
      {"$q_remove(1, i, i, P)",
       "constant 'P' cannot be written by '$q_remove'"},
      {"i = $q_full(1, P)", "constant 'P' cannot be written by '$q_full'"},
      {"$q_exam(1, 1, P, i)", "constant 'P' cannot be written by '$q_exam'"},
      {"$q_exam(1, 1, i, P)", "constant 'P' cannot be written by '$q_exam'"},
      {"$sreadmemb(P, 0, 1, \"0 1\")",
       "constant 'P' cannot be written by '$sreadmemb'"},
      {"$sreadmemh(P, 0, 1, \"0 1\")",
       "constant 'P' cannot be written by '$sreadmemh'"},
      {"i = $countdrivers(w, P)",
       "constant 'P' cannot be written by '$countdrivers'"},
      {"i = $countdrivers(w, i, P)",
       "constant 'P' cannot be written by '$countdrivers'"},
      {"i = $countdrivers(w, i, i, P)",
       "constant 'P' cannot be written by '$countdrivers'"},
      {"i = $countdrivers(w, i, i, i, P)",
       "constant 'P' cannot be written by '$countdrivers'"},
      {"i = $countdrivers(w, i, i, i, i, P)",
       "constant 'P' cannot be written by '$countdrivers'"},
      {"$async$and$array(mem, i, {i, P})",
       "constant 'P' cannot be written by '$async$and$array'"},
      {"$cast(P[3:0], i)", "constant 'P' cannot be written by '$cast'"},
  };
  ExpectEachWriteReported(
      "module m;\n  parameter int P = 1;\n  int fd, i;\n  string s;\n"
      "  logic [1:7] mem [1:3];\n  wire w;\n  initial ",
      7, kWrites);
}

TEST(ConstAssignElaboration,
     ASystemCallAcceptsAVariableWhereItWritesAndAConstantWhereItReads) {
  ExpectNoError(
      "module m;\n  parameter int P = 1;\n  parameter string F = \"m.txt\";\n"
      "  int fd, i, v, seed;\n  string s;\n  logic [1:7] mem [1:3];\n"
      "  wire w;\n  initial begin\n"
      "    $swrite(s, \"%d\", P);\n    $swriteb(s, P);\n    $swriteh(s, P);\n"
      "    $swriteo(s, P);\n    $sformat(s, \"%d\", P);\n"
      "    i = $fgets(s, P);\n    i = $fscanf(P, \"%d\", v);\n"
      "    i = $sscanf(F, \"%d\", v);\n    i = $fread(v, P);\n"
      "    i = $ferror(P, s);\n    $readmemb(F, mem, P);\n"
      "    $readmemh(F, mem, P, P);\n    i = $value$plusargs(\"n=%d\", v);\n"
      "    $cast(v, P);\n    i = $random(seed);\n"
      "    i = $dist_uniform(seed, P, 9);\n    i = $dist_normal(seed, P, P);\n"
      "    i = $dist_exponential(seed, P);\n    i = $dist_poisson(seed, P);\n"
      "    i = $dist_chi_square(seed, P);\n    i = $dist_t(seed, P);\n"
      "    i = $dist_erlang(seed, P, P);\n    $q_initialize(P, P, P, v);\n"
      "    $q_add(P, P, P, v);\n    $q_remove(P, v, v, v);\n"
      "    i = $q_full(P, v);\n    $q_exam(P, P, v, v);\n"
      "    $sreadmemb(mem, P, P, F);\n    $sreadmemh(mem, P, P, F);\n"
      "    i = $countdrivers(w, v, v, v, v, v);\n  end\nendmodule\n");
}

TEST(ConstAssignElaboration,
     EveryPlaTaskReportsAConstantOutputTermAndReadsAConstantInputTerm) {
  for (const char* task :
       {"$async$and$array", "$async$nand$array", "$async$or$array",
        "$async$nor$array", "$sync$and$array", "$sync$nand$array",
        "$sync$or$array", "$sync$nor$array", "$async$and$plane",
        "$async$nand$plane", "$async$or$plane", "$async$nor$plane",
        "$sync$and$plane", "$sync$nand$plane", "$sync$or$plane",
        "$sync$nor$plane"}) {
    SCOPED_TRACE(task);
    const std::string kPrelude =
        "module m;\n  parameter logic P = 1'b0;\n  logic [1:7] mem [1:3];\n"
        "  logic a, b;\n  initial " +
        std::string(task);
    ElabFixture f;
    ElaborateSrc(kPrelude + "(mem, a, P);\nendmodule\n", f);
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        std::string("constant 'P' cannot be written by '") + task + "'", 5,
        "6.20"));
    ExpectNoError(kPrelude + "(mem, P, b);\nendmodule\n");
  }
}

TEST(ConstAssignElaboration, AnArrayMethodThatChangesItsArrayReportsAConstant) {
  const BuiltInWrite kWrites[] = {
      {"q.push_back(3)", "assignment to constant 'q'"},
      {"q.push_front(0)", "assignment to constant 'q'"},
      {"i = q.pop_back()", "assignment to constant 'q'"},
      {"i = q.pop_front()", "assignment to constant 'q'"},
      {"q.insert(0, 3)", "assignment to constant 'q'"},
      {"q.delete(0)", "assignment to constant 'q'"},
      {"q.delete()", "assignment to constant 'q'"},
      {"d.delete()", "assignment to constant 'd'"},
      {"a.delete(\"x\")", "assignment to constant 'a'"},
      {"F.sort()", "assignment to constant 'F'"},
      {"F.rsort()", "assignment to constant 'F'"},
      {"F.reverse()", "assignment to constant 'F'"},
      {"F.shuffle()", "assignment to constant 'F'"},
      {"F.sort() with (item)", "assignment to constant 'F'"},
      {"N[0].sort()", "assignment to constant 'N'"},
      {"q.delete", "assignment to constant 'q'"},
      {"i = q.pop_back", "assignment to constant 'q'"},
      {"F.sort", "assignment to constant 'F'"},
      {"F.sort with (item)", "assignment to constant 'F'"},
      {"N[0].reverse", "assignment to constant 'N'"},
      {"hs.reverse()", "assignment to constant 'hs'"},
      {"hs.reverse", "assignment to constant 'hs'"},
  };
  ExpectEachWriteReported(
      "module m;\n  const int q[$] = '{1, 2};\n  const int d[] = '{1, 2};\n"
      "  const int a[string] = '{\"x\": 1};\n  parameter int F[2] = '{2, 1};\n"
      "  localparam int N[2][2] = '{'{2, 1}, '{4, 3}};\n  class C;\n"
      "  endclass\n  const C hs[2] = '{null, null};\n  int i;\n  initial ",
      11, kWrites);
}

TEST(ConstAssignElaboration,
     AnArrayMethodAcceptsAVariableArrayAndAConstantItOnlyReads) {
  const char* const kAccepted[] = {
      "module m;\n  int vq[$];\n  int vd[];\n  int va[string];\n  int vf[2];\n"
      "  const int q[$] = '{1, 2};\n  parameter int F[2] = '{2, 1};\n"
      "  int i;\n  initial begin\n    vq.push_back(3);\n    vq.push_front(0);\n"
      "    i = vq.pop_back();\n    i = vq.pop_front();\n    vq.insert(0, 3);\n"
      "    vq.delete(0);\n    vq.delete();\n    vd.delete();\n"
      "    va.delete(\"x\");\n    vf.sort();\n    vf.rsort();\n"
      "    vf.reverse();\n    vf.shuffle();\n    i = q.size();\n"
      "    i = F.sum();\n    i = q[0];\n    vq.delete;\n    i = vq.pop_back;\n"
      "    vf.sort;\n    vf.sort with (item);\n    i = F.sum;\n"
      "    i = q.size;\n  end\nendmodule\n",
      "module m;\n  class C;\n    int n;\n"
      "    function void push_back(int x); n = x; endfunction\n"
      "    function void sort(); n = 0; endfunction\n  endclass\n"
      "  const C h = new;\n  const C hs[2] = '{null, null};\n"
      "  initial begin\n    h.push_back(1);\n    h.sort();\n    h.sort;\n"
      "    hs[0].push_back(1);\n    hs[1].sort();\n    hs[1].sort;\n"
      "  end\nendmodule\n",
  };
  for (const char* src : kAccepted) ExpectNoError(src);
}

TEST(ConstAssignElaboration,
     AnAssociativeArrayTraversalReportsAConstantAsItsIndex) {
  const BuiltInWrite kWrites[] = {
      {"i = aa.first(P)", "constant 'P' cannot be written by 'first'"},
      {"i = aa.last(P)", "constant 'P' cannot be written by 'last'"},
      {"i = aa.next(P)", "constant 'P' cannot be written by 'next'"},
      {"i = aa.prev(P)", "constant 'P' cannot be written by 'prev'"},
      {"i = aa.first(c)", "constant 'c' cannot be written by 'first'"},
      {"i = an[0].next(P)", "constant 'P' cannot be written by 'next'"},
  };
  ExpectEachWriteReported(
      "module m;\n  parameter int P = 1;\n  const int c = 1;\n"
      "  int aa[int];\n  int an[2][int];\n  int i;\n  initial ",
      7, kWrites);
}

TEST(ConstAssignElaboration,
     ATraversalOrEnumMethodAcceptsAVariableIndexAndAConstantItOnlyReads) {
  ExpectNoError(
      "module m;\n  parameter int P = 1;\n  typedef enum {A, B, C} e_t;\n"
      "  e_t e;\n  e_t ea[2];\n  int aa[int];\n  int k, i;\n  class H;\n"
      "    function int first(input int x); return x; endfunction\n"
      "    function int next(input int x); return x; endfunction\n"
      "  endclass\n  H h;\n  initial begin\n    i = aa.first(k);\n"
      "    i = aa.last(k);\n    i = aa.next(k);\n    i = aa.prev(k);\n"
      "    e = e.next(P);\n    e = e.prev(P);\n    e = ea[0].next(P);\n"
      "    i = h.first(P);\n    i = h.next(P);\n    i = aa[P];\n  end\n"
      "endmodule\n");
}

TEST(ConstAssignElaboration, AScopeRandomizeReportsAConstantItWouldAssign) {
  const BuiltInWrite kWrites[] = {
      {"i = std::randomize(P)",
       "constant 'P' cannot be written by 'std::randomize'"},
      {"i = std::randomize(v, P)",
       "constant 'P' cannot be written by 'std::randomize'"},
      {"i = randomize(P)", "constant 'P' cannot be written by 'randomize'"},
      {"i = std::randomize(c) with { c > 0; }",
       "constant 'c' cannot be written by 'std::randomize'"},
  };
  ExpectEachWriteReported(
      "module m;\n  parameter int P = 1;\n  const int c = 1;\n  int i, v;\n"
      "  initial ",
      5, kWrites);
}

TEST(ConstAssignElaboration,
     AScopeRandomizeAcceptsAVariableAndAConstantInItsConstraint) {
  ExpectNoError(
      "module m;\n  parameter int P = 1;\n  int i, v;\n  initial begin\n"
      "    i = std::randomize(v) with { v < P; };\n    i = randomize(v);\n"
      "  end\nendmodule\n");
  ExpectNoError(
      "module m;\n  parameter int P = 1;\n  int i;\n"
      "  function int randomize(input int x); return x; endfunction\n"
      "  initial i = randomize(P);\nendmodule\n");
}

TEST(ConstAssignElaboration,
     AnEnumerationConstantWrittenOutsideAnAssignmentStatementIsReported) {
  const BuiltInWrite kWrites[] = {
      {"A++", "assignment to constant 'A'"},
      {"--A", "assignment to constant 'A'"},
      {"i = (A = B)", "assignment to constant 'A'"},
      {"t(A)",
       "constant 'A' cannot be the actual of output argument 'o' of 't'"},
      {"$cast(A, 1)", "constant 'A' cannot be written by '$cast'"},
      {"$cast($unit::A, 1)",
       "constant '$unit::A' cannot be written by '$cast'"},
      {"p::X = p::Y", "assignment to constant 'p::X'"},
      {"$cast(p::X, 1)", "constant 'p::X' cannot be written by '$cast'"},
  };
  ExpectEachWriteReported(
      "package p;\n  typedef enum {X, Y} pe_t;\nendpackage\n"
      "typedef enum {A, B} e_t;\nmodule m;\n  int i;\n"
      "  task t(output e_t o); o = B; endtask\n  initial ",
      8, kWrites);
}

TEST(ConstAssignElaboration,
     AnEnumerationConstantOfAModuleOrAnImportIsReportedWhereverItIsWritten) {
  const BuiltInWrite kWrites[] = {
      {"L0++", "assignment to constant 'L0'"},
      {"$cast(L1, 1)", "constant 'L1' cannot be written by '$cast'"},
      {"V0++", "assignment to constant 'V0'"},
      {"X++", "assignment to constant 'X'"},
      {"$cast(Y, 1)", "constant 'Y' cannot be written by '$cast'"},
      {"$cast(u.CA, 1)", "constant 'u.CA' cannot be written by '$cast'"},
      {"u.CA = u.CB", "assignment to constant 'u.CA'"},
  };
  ExpectEachWriteReported(
      "package p;\n  typedef enum {X, Y} pe_t;\nendpackage\nmodule c;\n"
      "  typedef enum {CA, CB} ce_t;\nendmodule\nmodule m;\n  import p::*;\n"
      "  typedef enum {L0, L1} l_t;\n  enum {V0, V1} v;\n  c u();\n"
      "  int i;\n  initial ",
      13, kWrites);
}

TEST(ConstAssignElaboration,
     AnEnumerationConstantOfAClassOrABlockIsReportedWhereverItIsWritten) {
  ElabFixture f;
  ElaborateSrc(
      "typedef enum {A, B} e_t;\n"
      "class K;\n"
      "  typedef enum {K0, K1} k_t;\n"
      "  enum {P0, P1} pv;\n"
      "  function void f();\n"
      "    K0++;\n"
      "    $cast(P1, 1);\n"
      "    K1 = K0;\n"
      "    A++;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  initial begin\n"
      "    enum {S0, S1} w;\n"
      "    S0++;\n"
      "    $cast(K::K0, 1);\n"
      "  end\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  EXPECT_TRUE(ReportedError(diags, "assignment to constant 'K0'", 6, "6.20"));
  EXPECT_TRUE(ReportedError(diags, "constant 'P1' cannot be written by '$cast'",
                            7, "6.20"));
  EXPECT_TRUE(ReportedError(
      diags, "assignment of constant 'K1', which is not a variable", 8,
      "10.4"));
  EXPECT_TRUE(ReportedError(diags, "assignment to constant 'A'", 9, "6.20"));
  EXPECT_TRUE(ReportedError(diags, "assignment to constant 'S0'", 15, "6.20"));
  EXPECT_TRUE(ReportedError(
      diags, "constant 'K::K0' cannot be written by '$cast'", 16, "6.20"));
}

TEST(ConstAssignElaboration,
     AnEnumerationVariableOrAShadowingNameWrittenThroughACallIsAccepted) {
  ExpectNoError(
      "typedef enum {A, B} e_t;\nmodule m;\n  e_t e;\n  int i;\n"
      "  task t(output e_t o); o = B; endtask\n  initial begin\n"
      "    t(e);\n    $cast(e, 1);\n    i = A + 1;\n    e = A;\n"
      "    begin\n      int A;\n      A = 1;\n      A++;\n"
      "      $cast(A, 1);\n    end\n  end\nendmodule\n");
  ExpectNoError(
      "class K;\n  typedef enum {K0, K1} k_t;\n  k_t kv;\n"
      "  function void f();\n    int K0;\n    K0 = 1;\n    K0++;\n"
      "    $cast(kv, 1);\n    kv = K1;\n  endfunction\nendclass\n"
      "module m;\nendmodule\n");
}

TEST(ConstAssignElaboration,
     AConstantActualOfAWritingFormalIsReportedThroughEveryCalleeName) {
  const BuiltInWrite kWrites[] = {
      {"p::pt(P)",
       "constant 'P' cannot be the actual of output argument 'o' of 'pt'"},
      {"$unit::ut(P)",
       "constant 'P' cannot be the actual of output argument 'o' of 'ut'"},
      {"C::sf(P)",
       "constant 'P' cannot be the actual of output argument 'o' of 'sf'"},
      {"h.mf(P)",
       "constant 'P' cannot be the actual of output argument 'o' of 'mf'"},
      {"hs[0].mf(P)",
       "constant 'P' cannot be the actual of output argument 'o' of 'mf'"},
      {"h.next.mf(P)",
       "constant 'P' cannot be the actual of output argument 'o' of 'mf'"},
      {"u.ct(P)",
       "constant 'P' cannot be the actual of ref argument 'o' of 'ct'"},
      {"u.w.gt(P)",
       "constant 'P' cannot be the actual of output argument 'o' of 'gt'"},
      {"$root.m.u.ct(P)",
       "constant 'P' cannot be the actual of ref argument 'o' of 'ct'"},
      {"iu.it(P)",
       "constant 'P' cannot be the actual of inout argument 'o' of 'it'"},
      {"vi.it(P)",
       "constant 'P' cannot be the actual of inout argument 'o' of 'it'"},
  };
  ExpectEachWriteReported(
      "package p;\n  task pt(output int o); o = 1; endtask\nendpackage\n"
      "interface ifc;\n  task it(inout int o); o = 1; endtask\nendinterface\n"
      "module g;\n  task gt(output int o); o = 1; endtask\nendmodule\n"
      "module c;\n  task automatic ct(ref int o); o = 1; endtask\n  g w();\n"
      "endmodule\nclass C;\n"
      "  static function void sf(output int o); o = 1; endfunction\n"
      "  function void mf(output int o); o = 1; endfunction\n  C next;\n"
      "endclass\ntask ut(output int o); o = 1; endtask\nmodule m;\n"
      "  parameter int P = 1;\n  ifc iu();\n  c u();\n  C h = new;\n"
      "  C hs[2];\n  virtual ifc vi = iu;\n  initial ",
      27, kWrites);
}

TEST(ConstAssignElaboration,
     AConstantActualOfAWritingFormalIsReportedInAClassAPackageAndAPort) {
  ElabFixture f;
  ElaborateSrc(
      "class B;\n"
      "  function void bf(output int o); o = 1; endfunction\n"
      "endclass\n"
      "class D #(int N = 1) extends B;\n"
      "  function void df(output int o); o = 1; endfunction\n"
      "  function void f();\n"
      "    this.df(N);\n"
      "    super.bf(N);\n"
      "    this.bf(N);\n"
      "  endfunction\n"
      "endclass\n"
      "class F;\n"
      "  localparam int L = 1;\n"
      "  extern function void f();\n"
      "  function void ff(output int o); o = 1; endfunction\n"
      "endclass\n"
      "function void F::f();\n"
      "  this.ff(L);\n"
      "endfunction\n"
      "package p;\n"
      "  task pt(output int o); o = 1; endtask\n"
      "endpackage\n"
      "package q;\n"
      "  parameter int Q = 1;\n"
      "  function void f();\n"
      "    p::pt(Q);\n"
      "  endfunction\n"
      "endpackage\n"
      "interface ifc;\n"
      "  task it(output int o); o = 1; endtask\n"
      "endinterface\n"
      "module k(ifc ip);\n"
      "  parameter int K = 1;\n"
      "  initial ip.it(K);\n"
      "endmodule\n"
      "module m;\n"
      "  ifc iu();\n"
      "  k kk(iu);\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  EXPECT_TRUE(ReportedError(
      diags, "constant 'N' cannot be the actual of output argument 'o' of 'df'",
      7, "6.20"));
  EXPECT_TRUE(ReportedError(
      diags, "constant 'N' cannot be the actual of output argument 'o' of 'bf'",
      8, "6.20"));
  EXPECT_TRUE(ReportedError(
      diags, "constant 'N' cannot be the actual of output argument 'o' of 'bf'",
      9, "6.20"));
  EXPECT_TRUE(ReportedError(
      diags, "constant 'L' cannot be the actual of output argument 'o' of 'ff'",
      18, "6.20"));
  EXPECT_TRUE(ReportedError(
      diags, "constant 'Q' cannot be the actual of output argument 'o' of 'pt'",
      26, "6.20"));
  EXPECT_TRUE(ReportedError(
      diags, "constant 'K' cannot be the actual of output argument 'o' of 'it'",
      34, "6.20"));
}

TEST(ConstAssignElaboration,
     AConstantActualOfAnInputFormalIsAcceptedThroughEveryCalleeName) {
  ExpectNoError(
      "package p;\n  task t(input int i); endtask\nendpackage\n"
      "interface ifc;\n  task t(input int i); endtask\nendinterface\n"
      "module c;\n  task t(input int i); endtask\nendmodule\n"
      "class C;\n  static function void s(input int i); endfunction\n"
      "  function void t(input int i); endfunction\nendclass\n"
      "task ut(input int i); endtask\nmodule m;\n  parameter int P = 1;\n"
      "  int v;\n  ifc iu();\n  c u();\n  C h = new;\n"
      "  virtual ifc vi = iu;\n  task t(output int o); o = 1; endtask\n"
      "  task s(output int o); o = 1; endtask\n"
      "  task ut(output int o); o = 1; endtask\n  initial begin\n"
      "    p::t(P);\n    C::s(P);\n    h.t(P);\n    u.t(P);\n"
      "    iu.t(P);\n    vi.t(P);\n    $root.m.u.t(P);\n"
      "    $unit::ut(P);\n    t(v);\n  end\nendmodule\n");
  ExpectNoError(
      "module m;\n  task t(output int o); o = 1; endtask\n  class K;\n"
      "    localparam int L = 1;\n"
      "    function void t(input int i); endfunction\n"
      "    function void f();\n      this.t(L);\n      t(L);\n"
      "    endfunction\n  endclass\nendmodule\n");
}

}  // namespace
