#include <gtest/gtest.h>

#include <format>
#include <initializer_list>
#include <string>
#include <string_view>

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

TEST(InstanceOverrideOperands, ForbiddenOperandInAnInstanceOverrideIsReported) {
  for (const Host& host : kHosts) {
    for (std::string_view target : host.targets) {
      const std::string kMessage = std::format(
          "override of parameter 'P' of '{}' is not a constant expression",
          target);
      for (std::string_view value :
           {"v", "w", "top.lp", "K::n", "T::n", "pk::pv", "nf()"}) {
        for (const std::string& instance :
             {NamedInstance(target, value), OrderedInstance(target, value)}) {
          SCOPED_TRACE(std::format("{}: {}", host.name, instance));
          ExpectReportedAtTheInstance(HostDesign(host, instance), kMessage);
        }
      }
    }
  }
}

TEST(InstanceOverrideOperands, AllowedOperandInAnInstanceOverrideIsAccepted) {
  for (const Host& host : kHosts) {
    for (std::string_view target : host.targets) {
      for (std::string_view value :
           {"lp", "pk::pp", "E1", "cf()", "cf() + 1", "$bits(v)"}) {
        for (const std::string& instance :
             {NamedInstance(target, value), OrderedInstance(target, value)}) {
          SCOPED_TRACE(std::format("{}: {}", host.name, instance));
          ExpectClean(HostDesign(host, instance));
        }
      }
    }
  }
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
    "int", "e_t", "K", "T", "enum {A}", "struct packed { bit a; }"};

TEST(InstanceOverrideOperands,
     DataTypeGivenToAValueParameterInAnInstanceOverrideIsReported) {
  for (const Host& host : kHosts) {
    for (std::string_view target : host.targets) {
      const std::string kMessage = std::format(
          "override of value parameter 'P' of '{}' is a data type, not an "
          "expression",
          target);
      for (std::string_view type : kDataTypes) {
        for (const std::string& instance :
             {NamedInstance(target, type), OrderedInstance(target, type)}) {
          SCOPED_TRACE(std::format("{}: {}", host.name, instance));
          ExpectReportedAtTheInstance(HostDesign(host, instance), kMessage);
        }
      }
    }
  }
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
