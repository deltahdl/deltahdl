#include <gtest/gtest.h>

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <string>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

std::string InModule(const std::string& declaration, const std::string& item) {
  return "module m(a);\n  " + declaration +
         " sp = 3; interface class I #(type T); endclass\n  " + item +
         "\nendmodule\n";
}

const char* const kRangedDeclarations[] = {
    "input [sp:0] a;",
    "input [3:sp] a;",
    "input a [sp];",
    "input a; wire [sp:0] w;",
    "input a; tri [0:sp] w;",
    "input a; wire [3:0][sp:0] w;",
    "input a; wire w [sp:0];",
    "input a; logic [sp:0] d;",
    "input a; logic [7:0] d [2][sp];",
    "input a; logic d [0:sp];",
    "input a; int d [$:sp];",
    "input a; logic [int'(sp):0] d;",
    "input a; logic [sp'(1):0] d;",
    "input a; logic [$clog2(sp):0] d;",
    "input a; logic [(1 ? sp : 0):0] d;",
    "input a; parameter [sp:0] P = 1;",
    "input a; parameter int P [sp] = '{1, 2, 3};",
    "input a; localparam [sp:0] L = 1;",
    "input a; parameter type T = logic [sp:0];",
    "input a; typedef logic [sp:0] t;",
    "input a; typedef int t [sp];",
    "input a; typedef struct packed { logic [sp:0] f; } t;",
    "input a; typedef struct { int f [sp]; } t;",
    "input a; typedef struct { struct { logic [sp:0] g; } f; } t;",
    "input a; union { logic [sp:0] f; int i; } d;",
    "input a; enum logic [sp:0] { A, B } d;",
    "input a; specparam [sp:0] t = 1;",
    "input a; specify specparam [sp:0] t = 1; endspecify",
    "input a; specify specparam [3:sp] t = 1; endspecify",
    "input a; initial begin logic [sp:0] d; end",
    "input a; initial begin int d [sp]; end",
    "input a; initial begin localparam [sp:0] L = 1; end",
    "input a; initial begin typedef logic [sp:0] t; end",
    "input a; initial for (logic [sp:0] i = 0; i < 2; i++);",
    "input a; task t(input logic [sp:0] x); endtask",
    "input a; task t; input [sp:0] x; endtask",
    "input a; task t(input int x [sp]); endtask",
    "input a; task t(); logic [sp:0] x; endtask",
    "input a; function logic [sp:0] f(); return 1; endfunction",
    "input a; function int f(logic [sp:0] x); return 1; endfunction",
    "input a; function int f(); int x [sp]; return 1; endfunction",
    "input a; import \"DPI-C\" function void f(input logic [sp:0] x);",
    "input a; class C; logic [sp:0] x; endclass",
    "input a; class C; int x [sp]; endclass",
    "input a; class C; typedef logic [sp:0] t; endclass",
    "input a; class C; function void f(logic [sp:0] x); endfunction endclass",
    "input a; class C #(parameter [sp:0] P = 1); endclass",
    "input a; class C #(type T = logic [sp:0]); endclass",
    "input a; class C #(type T = int); endclass C #(logic [sp:0]) c;",
    "input a; if (1) begin : g logic [sp:0] d; end",
    "input a; if (1) begin : g wire w [sp]; end",
    "input a; for (genvar i = 0; i < 1; i++) begin : g logic [sp:0] d; end",
    "input a; let l(logic [sp:0] x) = x;",
    "input a; property p(logic [sp:0] x); x; endproperty",
    "input a; sequence s; logic [sp:0] x; (1, x = 1); endsequence",
    "input a; covergroup g(logic [sp:0] x); endgroup",
    "input a; class C #(type T); typedef T t; endclass C #(bit [sp:0])::t d;",
    "input a; class C implements I #(bit [sp:0]); endclass",
    "input a; class C #(int P [sp] = '{1, 2, 3}); endclass",
    "input a; interface i; logic [sp:0] x; endinterface",
    "input a; module n; logic [sp:0] x; endmodule",
};

TEST(SpecparamUses, SpecparamInADeclarationRangeIsReportedEverywhere) {
  for (const char* item : kRangedDeclarations) {
    SCOPED_TRACE(item);
    ElabFixture f;
    ElaborateSrc(InModule("specparam", item), f, "m");
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "specparam 'sp' may not appear in a declaration "
                              "range specification",
                              3, "6.20.5"));
  }
}

TEST(SpecparamUses, ParameterInADeclarationRangeIsAcceptedEverywhere) {
  for (const std::string kItem : kRangedDeclarations) {
    if (kItem.find("specify") != std::string::npos) continue;
    SCOPED_TRACE(kItem);
    ElabFixture f;
    ElaborateSrc(InModule("parameter", kItem), f, "m");
    EXPECT_FALSE(f.has_errors);
  }
}

TEST(SpecparamUses, SpecparamOutsideADeclarationRangeIsAccepted) {
  for (const char* item :
       {"input a; logic [7:0] d; wire [3:0] w = d[sp:0];",
        "input a; int x = $bits(logic [sp:0]);",
        "input a; int x [4]; initial x[sp] = 1;",
        "input a; specify specparam [3:0] t = sp; endspecify",
        "input a; specify specparam PATHPULSE$ = (sp, sp); endspecify",
        "input a; struct { int sp; } s;"
        " initial begin logic [$bits(s.sp):0] d; end",
        "input a; function int f(); parameter sp = 2; logic [sp:0] d; "
        "return 1; endfunction"}) {
    SCOPED_TRACE(item);
    ElabFixture f;
    ElaborateSrc(InModule("specparam", item), f, "m");
    EXPECT_FALSE(f.has_errors);
  }
}

TEST(SpecparamUses, SeverityTaskShowsTheValueOfASpecparam) {
  ElabFixture f;
  ElaborateSrc(InModule("specparam", "input a; $info(\"%0d\", sp);"), f, "m");
  EXPECT_FALSE(f.has_errors);
  EXPECT_TRUE(ReportedWarning(
      f.diag.Diagnostics(), "elaboration INFO in scope 'm': 3", 3, "20.10.1"));
}

TEST(SpecparamUses, AttributeTakesTheValueOfASpecparam) {
  for (const char* items :
       {"specparam sp = 3; (* keep = sp *) int k;",
        "specify specparam sp = 3; endspecify (* keep = sp *) int k;",
        "(* keep = sp *) int k; specify specparam sp = 3; endspecify"}) {
    SCOPED_TRACE(items);
    ElabFixture f;
    const RtlirDesign* design = ElaborateSrc(
        std::string("module m; ") + items + " endmodule\n", f, "m");
    ASSERT_NE(design, nullptr);
    EXPECT_FALSE(f.has_errors);
    const std::vector<RtlirVariable>& variables =
        design->top_modules[0]->variables;
    const auto kKept = std::ranges::find(variables, "k", &RtlirVariable::name);
    ASSERT_NE(kKept, variables.end());
    ASSERT_FALSE(kKept->attrs.empty());
    EXPECT_EQ(kKept->attrs[0].resolved_value.value_or(INT64_MIN), 3);
  }
}

const char* const kReferences[] = {
    "initial #sp x = 1;",
    "initial x = sp;",
    "initial begin x <= sp + 1; end",
    "assign y = sp;",
    "assign #sp y = 1;",
    "wire [7:0] w = sp;",
    "wire #sp w;",
    "and #sp g1(z, y[0], y[1]);",
    "int i = sp;",
    "initial x = sp'(1);",
    "initial x = y[sp];",
    "function int f(); return sp; endfunction",
    "function int f(int b = sp); return b; endfunction",
    "task t(); #sp x = 1; endtask",
    "class C; int p = sp; endclass",
    "class C; function int f(); return sp; endfunction endclass",
    "if (1) begin : g initial x = sp; end",
    "if (sp) begin : g end",
    "let l = sp;",
    "initial assert (sp);",
    "property r1; @(x) ##sp 1; endproperty",
    "property r1; @(x) ##[0:sp] 1; endproperty",
    "property r1; @(x) n[*sp] ##1 n; endproperty",
    "property r1; @(x) nexttime[sp] n; endproperty",
    "property r1; @(x) always[0:sp] n; endproperty",
    "property r1; int i = sp; @(x) n ##1 i == 1; endproperty",
    "property r1; @(x) s_eventually[0:sp] n; endproperty",
    "initial x = $past(n, sp, , @(posedge n));",
    "clocking cb @(posedge n); input #sp z; endclocking",
    "clocking cb @(posedge n); input #1 output #sp x; endclocking",
    "clocking cb @(posedge n); default input #sp; input z; endclocking",
    "clocking cb @(posedge n); default output #sp; output x; endclocking",
    "(* keep = sp *) int k;",
    "(* keep = sp *) wire k;",
    "(* keep = sp *) specparam k = 1;",
    "(* keep = sp *) child c(p);",
    "(* keep = sp *) assign y = 1;",
    "(* keep = sp *) initial x = 1;",
    "(* keep = sp *) final x = 1;",
    "initial begin (* keep = sp *) x = 1; end",
    "initial x = y + (* keep = sp *) 1;",
    "class C; (* keep = sp *) int k; endclass",
    "struct { (* keep = sp *) int k; } s;",
    "alias y[sp:0] = y2[sp:0];",
    "pullup (y[sp]);",
    "assign y[0+:sp] = 1;",
    "function int f0(int b); return b; endfunction if (f0(sp)) begin end",
    "$info(\"%0d\", sp);",
    "sequence r1; int i; @(x) (n, i[sp] = 1); endsequence",
    "sequence r1; int i; @(x) first_match(n ##1 n, i[sp] = 1); endsequence",
    "property r1(z1); @(x) ##sp z1; endproperty",
    "covergroup g1; coverpoint x { bins b = {[0:sp]}; } endgroup",
    "covergroup g1; coverpoint x { bins b = (1 => sp); } endgroup",
    "covergroup g; cross x, n {bins c = binsof(x) intersect {sp};} endgroup",
    "interface i; int p = sp; endinterface",
    "child c(sp);",
    "specparam b = sp;",
    "specparam b = sp + 1, c = 2;",
    "specify specparam b = sp; endspecify",
    "specify specparam b = 1:sp:3; endspecify",
    "specify specparam PATHPULSE$ = (sp, 2); endspecify",
    "specify specparam PATHPULSE$ = (2, sp); endspecify",
    "specify specparam PATHPULSE$p$q = (sp, 2); endspecify",
    "specify (p => q) = sp; endspecify",
    "specify (p => q) = (1, sp); endspecify",
    "specify (p *> q) = {sp, 2'b1}; endspecify",
    "specify if (sp) (p => q) = 1; endspecify",
    "specify (posedge p => (q : sp)) = 1; endspecify",
    "specify $setup(p, posedge q, sp); endspecify",
    "specify $setup(p, posedge q &&& (q == sp), 1); endspecify",
    "specify $hold(posedge p &&& sp, q, 1); endspecify",
    "specify $setuphold(posedge p, q, 1, 2, n, sp); endspecify",
    "specify $setuphold(posedge p, q, 1, 2, n, , sp); endspecify",
    "specify $setuphold(posedge p, q, 1, 2, n, , , y[sp]); endspecify",
    "specify $recrem(posedge p, q, 1, 2, n, , , , y[sp]); endspecify",
    "specify $timeskew(posedge p, posedge q, 5, , sp); endspecify",
    "specify $timeskew(posedge p, posedge q, 5, , , sp); endspecify",
    "specify (v[sp] => q) = 1; endspecify",
    "specify (p => r[sp]) = 1; endspecify",
    "specify (p => r[1:sp]) = 1; endspecify",
    "specify $setup(v[sp], posedge q, 1); endspecify",
    "specify $hold(posedge q, v[sp], 1); endspecify",
    "specify pulsestyle_onevent r[sp]; endspecify",
};

constexpr char kOrderHead[] =
    "module child(input [7:0] a); endmodule\n"
    "module m(input p, input [3:0] v, output q, output [3:0] r);\n"
    "  int x; wire [7:0] y, y2; wire z; reg n;\n";

TEST(SpecparamUses, SpecparamReferencedBeforeItsDeclarationIsReported) {
  for (const std::string kReference : kReferences) {
    SCOPED_TRACE(kReference);
    ElabFixture f;
    ElaborateSrc(std::string(kOrderHead) + "  " + kReference +
                     "\n  specparam sp = 1;\nendmodule\n",
                 f, "m");
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        "specparam 'sp' is referenced before its declaration", 4, "6.20.5"));
  }
}

TEST(SpecparamUses, SpecparamReferencedAfterItsDeclarationIsAccepted) {
  for (const std::string kReference : kReferences) {
    SCOPED_TRACE(kReference);
    ElabFixture f;
    ElaborateSrc(std::string(kOrderHead) + "  specparam sp = 1;\n  " +
                     kReference + "\nendmodule\n",
                 f, "m");
    EXPECT_FALSE(f.has_errors);
  }
}

TEST(SpecparamUses, SpecparamReferencedWithinItsOwnDeclarationIsReported) {
  for (const char* item :
       {"specparam sp = sp;", "specparam sp = sp + 1;",
        "specparam b = sp, sp = 1;", "specparam sp = 1:sp:3;"}) {
    SCOPED_TRACE(item);
    ElabFixture f;
    ElaborateSrc(std::string("module m;\n  ") + item + "\nendmodule\n", f, "m");
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        "specparam 'sp' is referenced before its declaration", 2, "6.20.5"));
  }
  ElabFixture f;
  ElaborateSrc("module m;\n  specparam sp = 1, b = sp;\nendmodule\n", f, "m");
  EXPECT_FALSE(f.has_errors);
}

TEST(SpecparamUses, NameOtherThanALaterSpecparamIsAccepted) {
  for (const char* src :
       {"module m(input p, output q);\n  int x;\n  initial x = sp;\n"
        "  specify specparam sp = 3; (p => q) = sp; endspecify\nendmodule\n",
        "module m;\n  int x;\n  initial begin int sp; sp = 2; x = sp; end\n"
        "  specparam sp = 3;\nendmodule\n",
        "module m;\n  struct { int sp; } s;\n  initial s.sp = 1;\n"
        "  specparam sp = 3;\nendmodule\n",
        "module m;\n  function int f(int sp); return sp; endfunction\n"
        "  specparam sp = 3;\nendmodule\n",
        "module m;\n  struct { int sp; } s = '{sp: 1};\n"
        "  specparam sp = 3;\nendmodule\n"}) {
    SCOPED_TRACE(src);
    ElabFixture f;
    ElaborateSrc(src, f, "m");
    EXPECT_FALSE(f.has_errors);
  }
}

constexpr char kHolder[] =
    "module c(input p, output q); int v; specparam sp = 3;"
    " specify specparam sq = 4; (p => q) = sq; endspecify endmodule\n"
    "module d; c w(); if (1) begin : g c x(); end"
    " for (genvar i = 0; i < 2; i++) begin : h c y(); end"
    " if (0) begin : k end else if (1) begin : z c zz(); end"
    " if (1) if (1) begin : y2 c r2(); end"
    " case (1) 0: begin : s end default: begin : t c o(); end endcase"
    " endmodule\n";

constexpr char kTop[] =
    "module top; specparam st = 5; c u(); c a[1:0](); d n(); i j(); t l(); k "
    "q();"
    " if (1) begin : b i jj(); end endmodule\n";

struct OutsideUse {
  const char* path;
  const char* name;
};

constexpr OutsideUse kPaths[] = {
    {"top.st", "st"},          {"$root.top.st", "st"},
    {"top.u.sp", "sp"},        {"top.u.sq", "sq"},
    {"$root.top.u.sp", "sp"},  {"top.a[1].sp", "sp"},
    {"top.n.w.sp", "sp"},      {"top.n.g.x.sp", "sp"},
    {"top.n.h[1].y.sp", "sp"}, {"top.n.z.zz.sp", "sp"},
    {"top.n.y2.r2.sp", "sp"},  {"top.n.t.o.sp", "sp"},
    {"(1 + top.u.sp)", "sp"},  {"top.u.sp[1:0]", "sp"},
};

struct ReadingPlace {
  const char* where;
  const char* in_interface = "";
  const char* in_program = "";
  const char* in_module = "";
  const char* in_unit = "";
};

constexpr ReadingPlace kPlaces[] = {
    {.where = "interface", .in_interface = "int x; initial x = @;"},
    {.where = "generate block",
     .in_interface = "if (1) begin : e int x; initial x = @; end"},
    {.where = "program", .in_program = "int x; initial x = @;"},
    {.where = "class",
     .in_unit = "class C; function int f(); return @; endfunction endclass"},
    {.where = "class property", .in_unit = "class C; int x = @; endclass"},
    {.where = "unit", .in_unit = "function int f(); return @; endfunction"},
    {.where = "checker",
     .in_unit = "checker h; always_comb assert (@ == 3); endchecker"},
    {.where = "module", .in_module = "int x; initial x = @;"},
    {.where = "class in a module",
     .in_module = "class C; function int f(); return @; endfunction endclass"},
    {.where = "interface in a module",
     .in_module = "interface e; int x; initial x = @; endinterface"},
    {.where = "module block",
     .in_module = "if (1) begin : e int x; initial x = @; end"},
};

std::string Reading(const std::string& where, const std::string& path) {
  const ReadingPlace* place = std::ranges::find_if(
      kPlaces, [&](const ReadingPlace& p) { return where == p.where; });
  std::string text = std::string("interface i; ") + place->in_interface +
                     " endinterface\nprogram t; " + place->in_program +
                     " endprogram\nmodule k; " + place->in_module +
                     " endmodule\n" + place->in_unit + "\n";
  if (const std::size_t kAt = text.find('@'); kAt != std::string::npos) {
    text.replace(kAt, 1, path);
  }
  return text;
}

std::string Design(const std::string& where, const std::string& path) {
  return std::string(kHolder) + kTop + Reading(where, path);
}

TEST(SpecparamUses, SpecparamReadOutsideAModuleIsReported) {
  for (const char* where : {"interface", "generate block", "program", "class",
                            "class property", "unit", "checker"}) {
    for (const OutsideUse& use : kPaths) {
      SCOPED_TRACE(std::string(where) + " " + use.path);
      ElabFixture f;
      const std::string kSrc = Design(where, use.path);
      ElaborateSrc(kSrc, f, "top");
      EXPECT_TRUE(ReportedError(
          f.diag.Diagnostics(),
          std::string("specparam '") + use.name +
              "' may be used only inside a module or a specify block",
          LineHolding(kSrc, use.path), "6.20.5"));
    }
  }
}

TEST(SpecparamUses, SpecparamReadInsideAModuleIsAccepted) {
  for (const char* where : {"module", "class in a module",
                            "interface in a module", "module block"}) {
    for (const OutsideUse& use : kPaths) {
      SCOPED_TRACE(std::string(where) + " " + use.path);
      ElabFixture f;
      ElaborateSrc(Design(where, use.path), f, "top");
      EXPECT_FALSE(f.has_errors);
    }
  }
}

TEST(SpecparamUses, VariableOfAModuleReadOutsideAModuleIsAccepted) {
  for (const char* where : {"interface", "generate block", "program", "class",
                            "class property", "unit"}) {
    SCOPED_TRACE(where);
    ElabFixture f;
    ElaborateSrc(Design(where, "top.u.v"), f, "top");
    EXPECT_FALSE(f.has_errors);
  }
}

TEST(SpecparamUses, SpecparamReadUpwardOutsideAModuleIsReported) {
  for (const char* where : {"interface", "generate block", "program"}) {
    for (const char* path : {"u.sp", "a[0].sp", "n.w.sp", "n.g.x.sp"}) {
      SCOPED_TRACE(std::string(where) + " " + path);
      ElabFixture f;
      const std::string kSrc = Design(where, path);
      ElaborateSrc(kSrc, f, "top");
      EXPECT_TRUE(ReportedError(
          f.diag.Diagnostics(),
          "specparam 'sp' may be used only inside a module or a specify block",
          LineHolding(kSrc, path), "6.20.5"));
    }
  }
}

TEST(SpecparamUses, SpecparamReadUpwardFromABoundInterfaceIsReported) {
  const std::string kSrc =
      "module c; specparam sp = 3; endmodule\n"
      "module other; endmodule\n"
      "module top; c u(); other o(); endmodule\n"
      "interface i; int x;\n  initial x = u.sp;\nendinterface\n"
      "interface j; endinterface\n"
      "bind other j bj();\n"
      "bind top i bi();\n";
  ElabFixture f;
  ElaborateSrc(kSrc, f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "specparam 'sp' may be used only inside a module "
                            "or a specify block",
                            LineHolding(kSrc, "u.sp"), "6.20.5"));
}

TEST(SpecparamUses, SpecparamReadUpwardFromAnInterfaceInABlockIsReported) {
  for (const char* block :
       {"if (1) begin : b i bi(); end", "if (0) begin : b end else i bi();",
        "if (0) begin : b end else begin : e i bi(); end",
        "case (1) 1: i bi(); endcase",
        "case (1) 0: begin : b end default: begin : e i bi(); end endcase",
        "for (genvar k = 0; k < 2; k++) begin : b i bi(); end"}) {
    SCOPED_TRACE(block);
    ElabFixture f;
    ElaborateSrc(
        std::string("interface i; int x; initial x = u.sp; endinterface\n"
                    "module c; specparam sp = 3; endmodule\n"
                    "module top; c u(); ") +
            block + " endmodule\n",
        f, "top");
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        "specparam 'sp' may be used only inside a module or a specify block", 1,
        "6.20.5"));
  }
}

TEST(SpecparamUses, SpecparamReadThroughAGenerateBlockIsReported) {
  for (const char* block :
       {"if (0) begin : b end else begin : e c u(); end",
        "if (0) begin : b end else if (1) begin : e c u(); end",
        "case (1) 1: begin : e c u(); end default: begin : b end endcase",
        "case (1) 0: begin : b end default: begin : e c u(); end endcase"}) {
    SCOPED_TRACE(block);
    ElabFixture f;
    ElaborateSrc(
        std::string("interface i; int x; initial x = top.e.u.sp; endinterface\n"
                    "module c; specparam sp = 3; endmodule\n"
                    "module top; i bi(); ") +
            block + " endmodule\n",
        f, "top");
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        "specparam 'sp' may be used only inside a module or a specify block", 1,
        "6.20.5"));
  }
}

TEST(SpecparamUses, SpecparamReadUpwardFromAnInterfaceBoundToAnInstance) {
  for (const char* bind :
       {"bind top.o i bi();", "bind top.b.o i bi();", "bind o i bi();"}) {
    SCOPED_TRACE(bind);
    const std::string kSrc =
        "interface i; int x; initial x = u.sp; endinterface\n"
        "module c; specparam sp = 3; endmodule\n"
        "module other; c u(); endmodule\n"
        "module top; other o(); if (1) begin : b other o(); end endmodule\n";
    ElabFixture f;
    ElaborateSrc(kSrc + bind + "\n", f, "top");
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        "specparam 'sp' may be used only inside a module or a specify block", 1,
        "6.20.5"));
  }
}

TEST(SpecparamUses, SpecparamReadFromTheRootPastALocalNameIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "interface i; struct { int st; } top; int x;\n"
      "  initial x = top.st;\n  initial x = $root.top.st;\nendinterface\n"
      "module top; specparam st = 3; i n(); endmodule\n",
      f, "top");
  constexpr char kMessage[] =
      "specparam 'st' may be used only inside a module or a specify block";
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kMessage, 3, "6.20.5"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kMessage, 2, "6.20.5"));
}

TEST(SpecparamUses, NameThatReachesNoSpecparamIsNotReported) {
  for (const char* src :
       {"interface i; int x; initial x = u.v; endinterface\n"
        "interface o; i n(); endinterface\n"
        "module c; int v; specparam sp = 3; endmodule\n"
        "module top; c u(); o o1(); o o2(); i n(); endmodule\n",
        "interface i; int x; initial x = top.u.sp; endinterface\n"
        "module top; nowhere u(); i n(); endmodule\n",
        "struct { int sp; } top;\n"
        "interface i; int x; initial x = $unit::top.sp; endinterface\n"
        "module top; specparam sp = 3; i n(); endmodule\n",
        "package p; struct { int sp; } top; endpackage\n"
        "interface i; int x; initial x = p::top.sp; endinterface\n"
        "module top; specparam sp = 3; i n(); endmodule\n",
        "class C; int sp; function C g(); return this; endfunction\n"
        "  function int f(); return g().sp; endfunction endclass\n"
        "module top; specparam sp = 3; endmodule\n",
        "class C; function int f(); return $root.top; endfunction endclass\n"
        "module top; specparam top = 3; endmodule\n",
        "interface i; int x; initial x = u.sp; endinterface\n"
        "module c; specparam sp = 3; endmodule\n"
        "module other; endmodule\n"
        "module top; other o(); endmodule\n"
        "bind nowhere i bi();\n"}) {
    SCOPED_TRACE(src);
    ElabFixture f;
    ElaborateSrc(src, f, "top");
    for (const Diagnostic& reported : f.diag.Diagnostics()) {
      EXPECT_NE(reported.subclause, "6.20.5");
    }
  }
}

TEST(SpecparamUses, SpecparamReadUpwardThroughAnEnclosingInterfaceIsReported) {
  const std::string kSrc =
      "module c; specparam sp = 3; endmodule\n"
      "interface inner; int x; initial x = u.sp; endinterface\n"
      "interface outer; inner n(); endinterface\n"
      "module top; c u(); outer o(); endmodule\n";
  ElabFixture f;
  ElaborateSrc(kSrc, f, "top");
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "specparam 'sp' may be used only inside a module or a specify block", 2,
      "6.20.5"));
}

TEST(SpecparamUses, MemberNamedAsAModuleSpecparamIsAcceptedOutsideAModule) {
  const char* const kMembers[] = {
      "interface i; struct { int sp; } u; int x; initial x = u.sp; "
      "endinterface\n",
      "interface i; struct { struct { int sp; } u; } top; int x;"
      " initial x = top.u.sp; endinterface\n",
      "interface i; if (1) begin : u int sp; end int x; initial x = u.sp; "
      "endinterface\n",
  };
  for (const char* member : kMembers) {
    SCOPED_TRACE(member);
    ElabFixture f;
    ElaborateSrc(std::string(kHolder) + kTop + member +
                     "program t; endprogram\nmodule k; endmodule\n",
                 f, "top");
    EXPECT_FALSE(f.has_errors);
  }
}

}  // namespace
