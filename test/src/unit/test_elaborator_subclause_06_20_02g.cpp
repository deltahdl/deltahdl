#include <gtest/gtest.h>

#include <format>
#include <initializer_list>
#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

constexpr std::string_view kDeclarations =
    "package pk;\n"
    "  int pv;\n"
    "  localparam int pp = 3;\n"
    "endpackage\n"
    "class K;\n"
    "  static int n = 1;\n"
    "  localparam int q = 5;\n"
    "endclass\n"
    "class Y #(type U = int, int W = 1);\n"
    "endclass\n"
    "module m #(int P = 0);\n"
    "endmodule\n"
    "interface interface_i #(int P = 0);\n"
    "endinterface\n"
    "program p #(int P = 0);\n"
    "endprogram\n"
    "module mt #(type U = int);\n"
    "endmodule\n"
    "function automatic int cf();\n"
    "  return 4;\n"
    "endfunction\n"
    "typedef enum {E0, E1} e_t;\n";

constexpr std::string_view kHostItems =
    "  int v;\n"
    "  wire w;\n"
    "  localparam int lp = 2;\n"
    "  function int nf();\n"
    "    return v;\n"
    "  endfunction\n";

struct Host {
  std::string_view name;
  std::string_view head;
  std::string_view open;
  std::string_view close;
  std::string_view tail;
  std::initializer_list<std::string_view> targets;
};

constexpr std::initializer_list<Host> kHosts = {
    {"module",
     "module top #(type T = K);\n",
     "",
     "",
     "endmodule\n",
     {"m", "interface_i", "p"}},
    {"generate block",
     "module top #(type T = K);\n",
     "  if (1) begin : g\n",
     "  end\n",
     "endmodule\n",
     {"m", "interface_i", "p"}},
    {"interface",
     "interface host #(type T = K);\n",
     "",
     "",
     "endinterface\nmodule top;\n  host h();\nendmodule\n",
     {"interface_i"}},
};

std::string HostDesign(const Host& host, std::string_view instance) {
  return std::format("{}{}{}{}    {}\n{}{}", kDeclarations, host.head,
                     kHostItems, host.open, instance, host.close, host.tail);
}

std::string NamedInstance(std::string_view target, std::string_view value) {
  return std::format("{} #(.P({})) probe();", target, value);
}

std::string OrderedInstance(std::string_view target, std::string_view value) {
  return std::format("{} #({}) probe();", target, value);
}

void ExpectClean(const std::string& src) {
  ElabFixture f;
  ElaborateSrc(src, f);
  for (const Diagnostic& diag : f.diag.Diagnostics()) {
    if (diag.severity == DiagSeverity::kError)
      ADD_FAILURE() << "line " << diag.loc.line << ": " << diag.message;
  }
}

void ExpectReportedAtTheInstance(const std::string& src,
                                 std::string_view message) {
  ElabFixture f;
  ElaborateSrc(src, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), message,
                            LineHolding(src, "probe("), "6.20.2"));
}

template <typename Check>
void ForEachWrittenForm(std::string_view target,
                        std::initializer_list<std::string_view> values,
                        const Check& check) {
  for (std::string_view value : values) {
    for (const std::string& instance :
         {NamedInstance(target, value), OrderedInstance(target, value)}) {
      check(instance);
    }
  }
}

template <typename Check>
void ForEachHostedInstance(std::initializer_list<std::string_view> values,
                           const Check& check) {
  for (const Host& host : kHosts) {
    for (std::string_view target : host.targets) {
      ForEachWrittenForm(target, values, [&](const std::string& instance) {
        SCOPED_TRACE(std::format("{}: {}", host.name, instance));
        check(target, HostDesign(host, instance));
      });
    }
  }
}

TEST(InstanceOverrideOperands, ForbiddenOperandInAnInstanceOverrideIsReported) {
  ForEachHostedInstance(
      {"v", "w", "top.lp", "K::n", "T::n", "pk::pv", "nf()", "Y#(byte, v)::W"},
      [](std::string_view target, const std::string& src) {
        ExpectReportedAtTheInstance(
            src, std::format("override of parameter 'P' of '{}' is not a "
                             "constant expression",
                             target));
      });
}

TEST(InstanceOverrideOperands, AllowedOperandInAnInstanceOverrideIsAccepted) {
  ForEachHostedInstance(
      {"lp", "pk::pp", "E1", "cf()", "cf() + 1", "$bits(v)", "K::q", "T::q",
       "Y#(byte, 2)::W", "Y#(.U(byte), .W(2))::W"},
      [](std::string_view, const std::string& src) { ExpectClean(src); });
}

TEST(InstanceOverrideOperands, GenvarInAnInstanceOverrideIsAccepted) {
  for (std::string_view target : {"m", "interface_i", "p"}) {
    for (const std::string& instance :
         {NamedInstance(target, "g"), OrderedInstance(target, "g")}) {
      SCOPED_TRACE(instance);
      ExpectClean(
          std::format("{}module top;\n"
                      "  for (genvar g = 0; g < 2; g++) begin : b\n"
                      "    {}\n"
                      "  end\n"
                      "endmodule\n",
                      kDeclarations, instance));
    }
  }
}

constexpr std::initializer_list<std::string_view> kDataTypes = {
    "int",
    "logic [7:0]",
    "e_t",
    "K",
    "T",
    "enum {A}",
    "struct packed { bit a; }"};

TEST(InstanceOverrideOperands,
     DataTypeGivenToAValueParameterInAnInstanceOverrideIsReported) {
  ForEachHostedInstance(
      kDataTypes, [](std::string_view target, const std::string& src) {
        ExpectReportedAtTheInstance(
            src, std::format("override of value parameter 'P' of '{}' is a "
                             "data type, not an expression",
                             target));
      });
}

TEST(InstanceOverrideOperands,
     DataTypeGivenToATypeParameterInAnInstanceOverrideIsAccepted) {
  for (std::string_view type : kDataTypes) {
    for (const std::string& instance :
         {std::format("mt #(.U({})) probe();", type),
          std::format("mt #({}) probe();", type)}) {
      SCOPED_TRACE(instance);
      ExpectClean(HostDesign(*kHosts.begin(), instance));
    }
  }
}

}  // namespace
