#include <gtest/gtest.h>

#include <cstdint>
#include <format>
#include <string>
#include <string_view>

#include "fixture_elaborator.h"
#include "fixture_simulator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(Elaboration, EnumRangeNExpandsNames) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  typedef enum {sub[3]} E1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  auto it = mod->enum_types.find("E1");
  ASSERT_NE(it, mod->enum_types.end());
  ASSERT_EQ(it->second.size(), 3u);
  EXPECT_EQ(it->second[0].name, "sub0");
  EXPECT_EQ(it->second[0].value, 0);
  EXPECT_EQ(it->second[1].name, "sub1");
  EXPECT_EQ(it->second[1].value, 1);
  EXPECT_EQ(it->second[2].name, "sub2");
  EXPECT_EQ(it->second[2].value, 2);
}

TEST(Elaboration, EnumRangeNWithValue) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  typedef enum {add=10, sub[3]} E1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  auto it = mod->enum_types.find("E1");
  ASSERT_NE(it, mod->enum_types.end());
  ASSERT_EQ(it->second.size(), 4u);
  EXPECT_EQ(it->second[0].name, "add");
  EXPECT_EQ(it->second[0].value, 10);
  EXPECT_EQ(it->second[1].name, "sub0");
  EXPECT_EQ(it->second[1].value, 11);
  EXPECT_EQ(it->second[2].name, "sub1");
  EXPECT_EQ(it->second[2].value, 12);
  EXPECT_EQ(it->second[3].name, "sub2");
  EXPECT_EQ(it->second[3].value, 13);
}

TEST(Elaboration, EnumRangeNMExpandsNames) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  typedef enum {jmp[6:8]} E1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  auto it = mod->enum_types.find("E1");
  ASSERT_NE(it, mod->enum_types.end());
  ASSERT_EQ(it->second.size(), 3u);
  EXPECT_EQ(it->second[0].name, "jmp6");
  EXPECT_EQ(it->second[0].value, 0);
  EXPECT_EQ(it->second[1].name, "jmp7");
  EXPECT_EQ(it->second[1].value, 1);
  EXPECT_EQ(it->second[2].name, "jmp8");
  EXPECT_EQ(it->second[2].value, 2);
}

TEST(Elaboration, EnumRangeNMWithValue) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  typedef enum {register[2:4] = 10} E1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  auto it = mod->enum_types.find("E1");
  ASSERT_NE(it, mod->enum_types.end());
  ASSERT_EQ(it->second.size(), 3u);
  EXPECT_EQ(it->second[0].name, "register2");
  EXPECT_EQ(it->second[0].value, 10);
  EXPECT_EQ(it->second[1].name, "register3");
  EXPECT_EQ(it->second[1].value, 11);
  EXPECT_EQ(it->second[2].name, "register4");
  EXPECT_EQ(it->second[2].value, 12);
}

TEST(Elaboration, EnumRangeNMDecrementing) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  typedef enum {cnt[5:3]} E1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  auto it = mod->enum_types.find("E1");
  ASSERT_NE(it, mod->enum_types.end());
  ASSERT_EQ(it->second.size(), 3u);
  EXPECT_EQ(it->second[0].name, "cnt5");
  EXPECT_EQ(it->second[0].value, 0);
  EXPECT_EQ(it->second[1].name, "cnt4");
  EXPECT_EQ(it->second[1].value, 1);
  EXPECT_EQ(it->second[2].name, "cnt3");
  EXPECT_EQ(it->second[2].value, 2);
}

TEST(Elaboration, EnumRangeNMEqualBoundsSingle) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  typedef enum {sub[3:3]} E1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  auto it = mod->enum_types.find("E1");
  ASSERT_NE(it, mod->enum_types.end());
  ASSERT_EQ(it->second.size(), 1u);
  EXPECT_EQ(it->second[0].name, "sub3");
  EXPECT_EQ(it->second[0].value, 0);
}

TEST(Elaboration, EnumRangeNWithValueOnRangedMember) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  typedef enum {sub[3] = 20} E1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  auto it = mod->enum_types.find("E1");
  ASSERT_NE(it, mod->enum_types.end());
  ASSERT_EQ(it->second.size(), 3u);
  EXPECT_EQ(it->second[0].name, "sub0");
  EXPECT_EQ(it->second[0].value, 20);
  EXPECT_EQ(it->second[1].name, "sub1");
  EXPECT_EQ(it->second[1].value, 21);
  EXPECT_EQ(it->second[2].name, "sub2");
  EXPECT_EQ(it->second[2].value, 22);
}

TEST(Elaboration, EnumRangeNZeroIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef enum {sub[0]} E1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "enum range count of 'sub' has to be an integer of one or more", 2,
      "6.19.2"));
}

TEST(Elaboration, EnumRangeNMNegativeIsError) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module top;\n"
      "  typedef enum {sub[-1:2]} E1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "enumeration range bound must be an integral number", 2, "6.19.2"));
}

TEST(Elaboration, EnumRangeBoundWithXOrZDigitIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef enum {r[4'bx1]} E1;\n"
      "  typedef enum {s[2'bz1:3]} E2;\n"
      "  typedef enum {t[1:4'bx0]} E3;\n"
      "  typedef enum {u[4'bx]} E4;\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  uint32_t line = 2;
  for (const char* name : {"r", "s", "t", "u"}) {
    EXPECT_TRUE(ReportedError(
        diags,
        std::format("enum range bound of '{}' has to be an integer, and a "
                    "number with an x or z digit is none",
                    name),
        line++, "6.19.2"));
  }
  EXPECT_FALSE(ReportedError(
      diags, "enum range count of 'u' has to be an integer of one or more", 5,
      "6.19.2"));
}

TEST(Elaboration, EnumRangeNOneProducesSingle) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  typedef enum {sub[1]} E1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  auto it = mod->enum_types.find("E1");
  ASSERT_NE(it, mod->enum_types.end());
  ASSERT_EQ(it->second.size(), 1u);
  EXPECT_EQ(it->second[0].name, "sub0");
  EXPECT_EQ(it->second[0].value, 0);
}

TEST(Elaboration, EnumRangeNMZeroBoundsAllowed) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  typedef enum {register[0:2]} E1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  auto it = mod->enum_types.find("E1");
  ASSERT_NE(it, mod->enum_types.end());
  ASSERT_EQ(it->second.size(), 3u);
  EXPECT_EQ(it->second[0].name, "register0");
  EXPECT_EQ(it->second[0].value, 0);
  EXPECT_EQ(it->second[1].name, "register1");
  EXPECT_EQ(it->second[1].value, 1);
  EXPECT_EQ(it->second[2].name, "register2");
  EXPECT_EQ(it->second[2].value, 2);
}

TEST(Elaboration, EnumRangeNMNegativeEndIsError) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module top;\n"
      "  typedef enum {sub[2:-1]} E1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "enumeration range bound must be an integral number", 2, "6.19.2"));
}

TEST(Elaboration, EnumRangeSecondLrmExample) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  typedef enum {register[2] = 1, register[2:4] = 10} E1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  auto it = mod->enum_types.find("E1");
  ASSERT_NE(it, mod->enum_types.end());
  ASSERT_EQ(it->second.size(), 5u);
  EXPECT_EQ(it->second[0].name, "register0");
  EXPECT_EQ(it->second[0].value, 1);
  EXPECT_EQ(it->second[1].name, "register1");
  EXPECT_EQ(it->second[1].value, 2);
  EXPECT_EQ(it->second[2].name, "register2");
  EXPECT_EQ(it->second[2].value, 10);
  EXPECT_EQ(it->second[3].name, "register3");
  EXPECT_EQ(it->second[3].value, 11);
  EXPECT_EQ(it->second[4].name, "register4");
  EXPECT_EQ(it->second[4].value, 12);
}

TEST(Elaboration, EnumRangeLrmExample) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  typedef enum {add=10, sub[5], jmp[6:8]} E1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  auto it = mod->enum_types.find("E1");
  ASSERT_NE(it, mod->enum_types.end());
  ASSERT_EQ(it->second.size(), 9u);
  EXPECT_EQ(it->second[0].name, "add");
  EXPECT_EQ(it->second[0].value, 10);
  EXPECT_EQ(it->second[1].name, "sub0");
  EXPECT_EQ(it->second[1].value, 11);
  EXPECT_EQ(it->second[5].name, "sub4");
  EXPECT_EQ(it->second[5].value, 15);
  EXPECT_EQ(it->second[6].name, "jmp6");
  EXPECT_EQ(it->second[6].value, 16);
  EXPECT_EQ(it->second[8].name, "jmp8");
  EXPECT_EQ(it->second[8].value, 18);
}

TEST(Elaboration, EnumRangesGenerateTheirConstantsInEveryPlace) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "typedef enum {cu[2] = 5} cu_e;\n"
          "package p; typedef enum {pk[1:3]} pk_e; endpackage\n"
          "class K; typedef enum {kc[3:1] = 7} k_e; endclass\n"
          "interface ifc; typedef enum {ii[2]} i_e; i_e v = ii1; endinterface\n"
          "module t;\n"
          "  typedef enum {x = 3, r[2], s[4:4], u} m_e;\n"
          "  m_e m;\n"
          "  ifc i();\n"
          "  function automatic int ff();\n"
          "    typedef enum {fn[2:0]} f_e;\n"
          "    f_e e = fn0;\n"
          "    return e;\n"
          "  endfunction\n"
          "  initial begin\n"
          "    m = m.last();\n"
          "    $display(\"%0d %0d %0d %0d %0d %0d %0d %0d %0d\", cu1, p::pk3,\n"
          "      K::kc1, i.v, ff(), r0, r1, s4, m);\n"
          "    $display(\"%s %s %0d %s\", m.name(), m.prev().name(), m.num(),\n"
          "      K::kc2.name());\n"
          "  end\n"
          "endmodule\n",
          f),
      "6 2 9 1 2 4 5 6 7\nu s4 5 kc2\n");
}

TEST(Elaboration, DISABLED_EnumRangeNameDuplicatingAnotherIsReported) {
  std::string src =
      "typedef enum {cu0, cu[2]} cu_e;\n"
      "package p; typedef enum {pk[1:3], pk2} pk_e; endpackage\n"
      "class K; typedef enum {kc[2], kc[1:0]} k_e; endclass\n"
      "module t;\n"
      "  typedef enum {a1, a[2] = 5} m_e;\n"
      "  function automatic void ff();\n"
      "    typedef enum {fn[3:1], fn[2]} f_e;\n"
      "  endfunction\n"
      "endmodule\n";
  ElabFixture f;
  ElaborateSrc(src, f);
  for (std::string_view at :
       {"} cu_e;", "} pk_e;", "} k_e;", "} m_e;", "} f_e;"}) {
    SCOPED_TRACE(at);
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "duplicate enum member name",
                              LineHolding(src, at), "6.19"));
  }
}

TEST(Elaboration, DISABLED_EnumRangeValuePastTheBaseTypeIsReported) {
  std::string src =
      "typedef enum bit [1:0] {cu[5]} cu_e;\n"
      "package p; typedef enum bit [1:0] {pk[3:7]} pk_e; endpackage\n"
      "class K; typedef enum bit [1:0] {kc[2] = 3} k_e; endclass\n"
      "module t;\n"
      "  typedef enum logic [2:0] {a = 6, b[1:0]} m_e;\n"
      "  function automatic void ff();\n"
      "    typedef enum bit {fn[0:2] = 0} f_e;\n"
      "  endfunction\n"
      "endmodule\n";
  ElabFixture f;
  ElaborateSrc(src, f);
  for (std::string_view at :
       {"} cu_e;", "} pk_e;", "} k_e;", "} m_e;", "} f_e;"}) {
    SCOPED_TRACE(at);
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "exceeds maximum representable value",
                              LineHolding(src, at), "6.19"));
  }
}

TEST(Elaboration, EnumRangesThatFitAndNameDistinctConstantsAreAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "typedef enum bit [1:0] {cu[4]} cu_e;\n"
      "package p; typedef enum bit [1:0] {pk[2:4], pk1x} pk_e; endpackage\n"
      "class K; typedef enum bit [1:0] {kc[1] = 3} k_e; endclass\n"
      "module t;\n"
      "  typedef enum logic [2:0] {a = 4, b[1:0], a0} m_e;\n"
      "  function automatic void ff();\n"
      "    typedef enum bit {fn[0:1] = 0} f_e;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
