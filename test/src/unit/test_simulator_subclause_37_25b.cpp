#include <gtest/gtest.h>

#include <algorithm>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class TypespecsOfARun : public VpiDesignRun {
 protected:
  static int KindOf(vpiHandle obj) {
    return obj == nullptr ? 0 : vpi_get(vpiType, obj);
  }

  static bool Same(vpiHandle a, vpiHandle b) {
    return a != nullptr && b != nullptr && vpi_compare_objects(a, b) != 0;
  }

  static std::vector<std::string> ConstsOf(vpiHandle typespec) {
    if (typespec == nullptr) return {"<no typespec>"};
    if (vpi_get(vpiType, typespec) != vpiEnumTypespec) return {"<not an enum>"};
    return NamesOf(vpiEnumConst, typespec);
  }

  static std::vector<std::string> ConstsOfTypeOf(vpiHandle obj) {
    if (obj == nullptr) return {"<no object>"};
    return ConstsOf(vpi_handle(vpiTypespec, obj));
  }

  static vpiHandle Unit() {
    for (vpiHandle package : ObjectsOf(vpiPackage, nullptr)) {
      if (vpi_get(vpiUnit, package) == 1) return package;
    }
    return nullptr;
  }

  static vpiHandle MemberType(vpiHandle aggregate, std::string_view member) {
    vpiHandle found = Named(vpiTypespecMember, aggregate, member);
    return found == nullptr ? nullptr : vpi_handle(vpiTypespec, found);
  }

  static std::vector<int> SizesOfRanges(vpiHandle typespec) {
    const std::vector<vpiHandle> kRanges = ObjectsOf(vpiRange, typespec);
    std::vector<int> sizes(kRanges.size());
    std::ranges::transform(kRanges, sizes.begin(), [](vpiHandle range) {
      return vpi_get(vpiSize, range);
    });
    return sizes;
  }

  static std::vector<int> LeftmostBoundsOf(vpiHandle typespec) {
    vpiHandle left = vpi_handle(vpiLeftRange, typespec);
    vpiHandle right = vpi_handle(vpiRightRange, typespec);
    std::vector<int> bounds;
    if (left != nullptr) bounds.push_back(IntegerOf(left));
    if (right != nullptr) bounds.push_back(IntegerOf(right));
    return bounds;
  }

  static std::string StringOf(vpiHandle obj, int format) {
    s_vpi_value value = {};
    value.format = format;
    vpi_get_value(obj, &value);
    return value.value.str == nullptr ? "" : value.value.str;
  }

  using PlacedConst = std::pair<std::string, vpiHandle>;

  std::vector<PlacedConst> ConstsOfEveryPlace(const std::string& base,
                                              const std::string& value) {
    auto body = [&](const char* name) {
      return base + " {" + name + " = " + value + "}";
    };
    Run("typedef enum " + body("U") + " u_t;\n" + "package pk; typedef enum " +
        body("P") + " p_t; endpackage\n" + "module top; typedef enum " +
        body("M") + " m_t;\n" + "  enum " + body("V") + " v; endmodule\n");
    const std::vector<PlacedConst> kPlaced = {
        {"unit typedef",
         Named(vpiEnumConst, Named(vpiTypedef, Unit(), "u_t"), "U")},
        {"package typedef",
         Named(vpiEnumConst, Named(vpiTypedef, By("pk"), "p_t"), "P")},
        {"module typedef",
         Named(vpiEnumConst, Named(vpiTypedef, By("top"), "m_t"), "M")},
        {"variable",
         Named(vpiEnumConst, vpi_handle(vpiTypespec, By("top.v")), "V")},
    };
    std::vector<PlacedConst> found;
    for (const auto& [place, constant] : kPlaced) {
      if (constant == nullptr) {
        ADD_FAILURE() << "no enum constant in the " << place;
      } else {
        found.emplace_back(place, constant);
      }
    }
    return found;
  }

  void ExpectEveryConstReads(const std::string& base, const std::string& value,
                             int format, const std::string& expected) {
    for (const auto& [place, constant] : ConstsOfEveryPlace(base, value)) {
      EXPECT_EQ(StringOf(constant, format), expected) << place;
    }
  }

  static void ExpectAliasChainThroughVariables(const std::string& scope) {
    vpiHandle half = vpi_handle(vpiTypespec, By(scope + ".h"));
    vpiHandle nib = vpi_handle(vpiTypespec, By(scope + ".n"));
    ASSERT_NE(half, nullptr);
    ASSERT_NE(nib, nullptr);
    EXPECT_STREQ(vpi_get_str(vpiName, half), "half_t");
    EXPECT_STREQ(vpi_get_str(vpiName, nib), "nib_t");
    EXPECT_TRUE(Same(vpi_handle(vpiTypedefAlias, half), nib));
    EXPECT_EQ(vpi_handle(vpiTypedefAlias, nib), nullptr);
  }
};

TEST_F(TypespecsOfARun, DISABLED_ANarrowLogicEnumConstReadsAtItsBaseWidth) {
  for (const auto& [place, constant] :
       ConstsOfEveryPlace("logic [7:0]", "8'hA5")) {
    EXPECT_EQ(StringOf(constant, vpiBinStrVal), "10100101") << place;
    s_vpi_value value = {};
    value.format = vpiVectorVal;
    vpi_get_value(constant, &value);
    ASSERT_NE(value.value.vector, nullptr) << place;
    EXPECT_EQ(value.value.vector[0].aval, 0xA5) << place;
    EXPECT_EQ(value.value.vector[0].bval, 0) << place;
  }
}

TEST_F(TypespecsOfARun, DISABLED_ABitEnumConstReadsAtItsBaseWidth) {
  ExpectEveryConstReads("bit [2:0]", "3'd5", vpiBinStrVal, "101");
}

TEST_F(TypespecsOfARun, DISABLED_ALongintEnumConstKeepsItsUpperBits) {
  ExpectEveryConstReads("longint", "64'h1000_0000_0000_0002", vpiHexStrVal,
                        "1000000000000002");
}

TEST_F(TypespecsOfARun, DISABLED_AWideLogicEnumConstKeepsItsUpperByte) {
  ExpectEveryConstReads("logic [39:0]", "40'h11_0000_0002", vpiHexStrVal,
                        "1100000002");
}

TEST_F(TypespecsOfARun, DISABLED_AFourStateEnumConstKeepsItsXAndZBits) {
  ExpectEveryConstReads("logic [3:0]", "4'b1x0z", vpiBinStrVal, "1x0z");
}

TEST_F(TypespecsOfARun, DISABLED_ASignedByteEnumConstIsSignExtended) {
  for (const auto& [place, constant] : ConstsOfEveryPlace("byte", "-2")) {
    EXPECT_EQ(IntegerOf(constant), -2) << place;
    EXPECT_EQ(StringOf(constant, vpiBinStrVal), "11111110") << place;
  }
}

TEST_F(TypespecsOfARun, DISABLED_AnIntEnumConstReadsThirtyTwoBits) {
  for (const auto& [place, constant] : ConstsOfEveryPlace("", "5")) {
    EXPECT_EQ(IntegerOf(constant), 5) << place;
    EXPECT_EQ(StringOf(constant, vpiBinStrVal), std::string(29, '0') + "101")
        << place;
  }
}

constexpr const char* kEnumsOfEveryScope =
    "typedef enum {UA, UB} u_t; enum {UC, UD} uw;\n"
    "package pk; typedef enum {PA, PB} p_t; enum {PC, PD} pw; endpackage\n"
    "interface ifc; typedef enum {IA, IB} i_t; i_t v; enum {IC, ID} w;\n"
    "endinterface\n"
    "program prg; typedef enum {GA, GB} g_t; g_t v; endprogram\n"
    "module top; ifc i(); prg g(); enum {MA, MB} w;\n"
    "  parameter enum {QA, QB} p = QB;\n"
    "  if (1) begin : blk typedef enum {BA, BB} b_t; b_t v; end\n"
    "endmodule\n";

using Names = std::vector<std::string>;

TEST_F(TypespecsOfARun, DISABLED_AUnitEnumTypedefIteratesItsConstants) {
  Run(kEnumsOfEveryScope);
  EXPECT_EQ(ConstsOf(Named(vpiTypedef, Unit(), "u_t")), (Names{"UA", "UB"}));
}

TEST_F(TypespecsOfARun, DISABLED_APackageEnumTypedefIteratesItsConstants) {
  Run(kEnumsOfEveryScope);
  EXPECT_EQ(ConstsOf(Named(vpiTypedef, By("pk"), "p_t")), (Names{"PA", "PB"}));
}

TEST_F(TypespecsOfARun, AnInterfaceEnumTypedefIteratesItsConstants) {
  Run(kEnumsOfEveryScope);
  EXPECT_EQ(ConstsOfTypeOf(By("top.i.v")), (Names{"IA", "IB"}));
}

TEST_F(TypespecsOfARun, AProgramEnumTypedefIteratesItsConstants) {
  Run(kEnumsOfEveryScope);
  EXPECT_EQ(ConstsOfTypeOf(By("top.g.v")), (Names{"GA", "GB"}));
}

TEST_F(TypespecsOfARun, AGenerateBlockEnumTypedefIteratesItsConstants) {
  Run(kEnumsOfEveryScope);
  EXPECT_EQ(ConstsOf(Named(vpiTypedef, By("top.blk"), "b_t")),
            (Names{"BA", "BB"}));
}

TEST_F(TypespecsOfARun,
       DISABLED_AnEnumVariableWrittenInPlaceIteratesItsConstants) {
  Run(kEnumsOfEveryScope);
  EXPECT_EQ(ConstsOfTypeOf(By("top.w")), (Names{"MA", "MB"})) << "module";
  EXPECT_EQ(ConstsOfTypeOf(By("top.i.w")), (Names{"IC", "ID"})) << "interface";
}

TEST_F(TypespecsOfARun,
       DISABLED_APackageOrUnitEnumVariableWrittenInPlaceIteratesItsConstants) {
  Run(kEnumsOfEveryScope);
  EXPECT_EQ(ConstsOfTypeOf(Named(vpiVariables, By("pk"), "pw")),
            (Names{"PC", "PD"}))
      << "package";
  EXPECT_EQ(ConstsOfTypeOf(Named(vpiVariables, Unit(), "uw")),
            (Names{"UC", "UD"}))
      << "unit";
}

TEST_F(TypespecsOfARun,
       DISABLED_AnEnumParameterWrittenInPlaceIteratesItsConstants) {
  Run(kEnumsOfEveryScope);
  EXPECT_EQ(ConstsOfTypeOf(Named(vpiParameter, By("top"), "p")),
            (Names{"QA", "QB"}));
}

TEST_F(TypespecsOfARun, ACheckerEnumTypedefIteratesItsConstants) {
  Run("checker chk; typedef enum {CA, CB} c_t; c_t v; "
      "endchecker\n"
      "module top; chk c(); endmodule\n");
  EXPECT_EQ(ConstsOfTypeOf(By("top.c.v")), (Names{"CA", "CB"}));
}

TEST_F(TypespecsOfARun, AnEnumConstReachesTheEnumTypespecItBelongsTo) {
  Run("module top;\n"
      "  typedef enum bit [1:0] {red, yellow, blue} "
      "primary_colors;\n"
      "  typedef enum {X, Y} other_e; typedef "
      "primary_colors colors;\n"
      "endmodule\n");
  vpiHandle top = By("top");
  vpiHandle primary = Named(vpiTypedef, top, "primary_colors");
  vpiHandle other = Named(vpiTypedef, top, "other_e");
  vpiHandle colors = Named(vpiTypedef, top, "colors");
  ASSERT_NE(primary, nullptr);
  ASSERT_NE(other, nullptr);
  ASSERT_NE(colors, nullptr);
  for (const char* name : {"red", "yellow", "blue"}) {
    EXPECT_TRUE(
        Same(vpi_handle(vpiEnumTypespec, Named(vpiEnumConst, primary, name)),
             primary))
        << name;
  }
  EXPECT_TRUE(Same(vpi_handle(vpiEnumTypespec, Named(vpiEnumConst, other, "Y")),
                   other));
  vpiHandle via_alias =
      vpi_handle(vpiEnumTypespec, Named(vpiEnumConst, colors, "red"));
  EXPECT_TRUE(Same(via_alias, colors) || Same(via_alias, primary));
}

TEST_F(TypespecsOfARun, ATimeTypedefsVariableReachesItAsATimeTypespec) {
  Run("module top; typedef time my_time; my_time t; "
      "endmodule\n");
  vpiHandle typespec = vpi_handle(vpiTypespec, By("top.t"));
  ASSERT_NE(typespec, nullptr);
  EXPECT_TRUE(Same(typespec, Named(vpiTypedef, By("top"), "my_time")));
  EXPECT_STREQ(vpi_get_str(vpiName, typespec), "my_time");
  EXPECT_EQ(vpi_get(vpiType, typespec), vpiTimeTypespec);
  vpiHandle time = vpi_handle(vpiTypedefAlias, typespec);
  EXPECT_EQ(KindOf(time), vpiTimeTypespec);
  EXPECT_EQ(time == nullptr ? nullptr : vpi_get_str(vpiName, time), nullptr);
}

TEST_F(TypespecsOfARun, ShortrealAndLongintTypespecsAreTheirOwnKinds) {
  Run("module top; typedef shortreal sr_t; typedef "
      "longint li_t;\n"
      "  shortreal s; longint l; endmodule\n");
  vpiHandle top = By("top");
  vpiHandle sr = Named(vpiTypedef, top, "sr_t");
  vpiHandle li = Named(vpiTypedef, top, "li_t");
  EXPECT_EQ(KindOf(sr), vpiShortRealTypespec);
  EXPECT_EQ(KindOf(li), vpiLongIntTypespec);
  EXPECT_STREQ(sr == nullptr ? nullptr : vpi_get_str(vpiName, sr), "sr_t");
  EXPECT_STREQ(li == nullptr ? nullptr : vpi_get_str(vpiName, li), "li_t");
  EXPECT_EQ(KindOf(vpi_handle(vpiTypespec, By("top.s"))), vpiShortRealTypespec);
  EXPECT_EQ(KindOf(vpi_handle(vpiTypespec, By("top.l"))), vpiLongIntTypespec);
}

TEST_F(TypespecsOfARun, AUnionTypedefIsAUnionTypespec) {
  Run("module top; typedef union { int i; bit b; } "
      "u_t;\n"
      "  typedef union packed { bit [3:0] a; bit [3:0] "
      "b; } pu_t;\n"
      "endmodule\n");
  vpiHandle top = By("top");
  for (const char* name : {"u_t", "pu_t"}) {
    vpiHandle typespec = Named(vpiTypedef, top, name);
    ASSERT_NE(typespec, nullptr) << name;
    EXPECT_EQ(vpi_get(vpiType, typespec), vpiUnionTypespec) << name;
    EXPECT_STREQ(vpi_get_str(vpiName, typespec), name);
  }
}

constexpr const char* kTypedefsOfEveryInstanceKind =
    "package pk; typedef bit pt; endpackage\n"
    "interface ifc; typedef bit it; it v; "
    "endinterface\n"
    "program prg; typedef bit gt; gt v; endprogram\n"
    "module top; typedef bit mt; mt v; ifc i(); prg "
    "g(); endmodule\n";

TEST_F(TypespecsOfARun, ATypespecReachesTheInstanceDeclaringIt) {
  Run(kTypedefsOfEveryInstanceKind);
  EXPECT_TRUE(
      Same(vpi_handle(vpiInstance, vpi_handle(vpiTypespec, By("top.v"))),
           By("top")));
  EXPECT_TRUE(Same(vpi_handle(vpiInstance, Named(vpiTypedef, By("pk"), "pt")),
                   By("pk")));
  EXPECT_TRUE(
      Same(vpi_handle(vpiInstance, vpi_handle(vpiTypespec, By("top.i.v"))),
           By("top.i")));
  EXPECT_TRUE(
      Same(vpi_handle(vpiInstance, vpi_handle(vpiTypespec, By("top.g.v"))),
           By("top.g")));
}

TEST_F(TypespecsOfARun, InterfaceAndProgramInstancesIterateTheirTypedefs) {
  Run(kTypedefsOfEveryInstanceKind);
  EXPECT_EQ(NamesOf(vpiTypedef, By("top.i")), (std::vector<std::string>{"it"}));
  EXPECT_EQ(NamesOf(vpiTypedef, By("top.g")), (std::vector<std::string>{"gt"}));
}

TEST_F(TypespecsOfARun, AMemberWrittenAsAUnionReachesItsOwnTypespec) {
  Run("module top;\n"
      "  typedef struct { union packed { bit [3:0] a; "
      "bit [3:0] b; } u;\n"
      "                   union { int i; shortreal r; "
      "} w; } s_t;\n"
      "endmodule\n");
  vpiHandle s = Named(vpiTypedef, By("top"), "s_t");
  ASSERT_NE(s, nullptr);
  vpiHandle u = MemberType(s, "u");
  vpiHandle w = MemberType(s, "w");
  ASSERT_NE(u, nullptr);
  ASSERT_NE(w, nullptr);
  EXPECT_EQ(vpi_get(vpiType, u), vpiUnionTypespec);
  EXPECT_EQ(vpi_get(vpiPacked, u), 1);
  EXPECT_EQ(vpi_get_str(vpiName, u), nullptr);
  EXPECT_EQ(NamesOf(vpiTypespecMember, u),
            (std::vector<std::string>{"a", "b"}));
  EXPECT_EQ(BoundsOf(MemberType(u, "a")), (std::vector<int>{3, 0}));
  EXPECT_EQ(vpi_get(vpiType, w), vpiUnionTypespec);
  EXPECT_EQ(vpi_get(vpiPacked, w), 0);
  EXPECT_EQ(KindOf(MemberType(w, "i")), vpiIntTypespec);
  EXPECT_EQ(KindOf(MemberType(w, "r")), vpiShortRealTypespec);
}

TEST_F(TypespecsOfARun, DISABLED_AMemberWrittenAsAnEnumReachesItsOwnTypespec) {
  Run("module top;\n"
      "  typedef struct { enum bit [1:0] {A, B} e; int "
      "x; } s_t;\n"
      "endmodule\n");
  vpiHandle s = Named(vpiTypedef, By("top"), "s_t");
  ASSERT_NE(s, nullptr);
  vpiHandle e = MemberType(s, "e");
  ASSERT_NE(e, nullptr);
  EXPECT_EQ(vpi_get(vpiType, e), vpiEnumTypespec);
  EXPECT_EQ(vpi_get_str(vpiName, e), nullptr);
  vpiHandle base = vpi_handle(vpiBaseTypespec, e);
  EXPECT_EQ(KindOf(base), vpiBitTypespec);
  EXPECT_EQ(BoundsOf(base), (std::vector<int>{1, 0}));
  EXPECT_EQ(NamesOf(vpiEnumConst, e), (std::vector<std::string>{"A", "B"}));
  EXPECT_EQ(IntsOf(vpiEnumConst, e), (std::vector<int>{0, 1}));
}

TEST_F(TypespecsOfARun, AKeywordTypedefAliasesThatKeywordsTypespec) {
  Run("module top;\n"
      "  typedef byte by_t; typedef shortint si_t; "
      "typedef int in_t;\n"
      "  typedef longint li_t; typedef integer ig_t; "
      "typedef time ti_t;\n"
      "  typedef bit bi_t; typedef logic lo_t; typedef "
      "reg re_t;\n"
      "  typedef real rl_t; typedef shortreal sr_t; "
      "typedef realtime rt_t;\n"
      "  typedef string st_t;\n"
      "endmodule\n");
  const std::pair<const char*, int> kAliases[] = {
      {"by_t", vpiByteTypespec},      {"si_t", vpiShortIntTypespec},
      {"in_t", vpiIntTypespec},       {"li_t", vpiLongIntTypespec},
      {"ig_t", vpiIntegerTypespec},   {"ti_t", vpiTimeTypespec},
      {"bi_t", vpiBitTypespec},       {"lo_t", vpiLogicTypespec},
      {"re_t", vpiLogicTypespec},     {"rl_t", vpiRealTypespec},
      {"sr_t", vpiShortRealTypespec}, {"rt_t", vpiRealTypespec},
      {"st_t", vpiStringTypespec},
  };
  vpiHandle top = By("top");
  for (const auto& [name, kind] : kAliases) {
    vpiHandle typedef_ts = Named(vpiTypedef, top, name);
    ASSERT_NE(typedef_ts, nullptr) << name;
    EXPECT_EQ(vpi_get(vpiType, typedef_ts), kind) << name;
    vpiHandle keyword = vpi_handle(vpiTypedefAlias, typedef_ts);
    ASSERT_NE(keyword, nullptr) << name;
    EXPECT_EQ(vpi_get(vpiType, keyword), kind) << name;
    EXPECT_EQ(vpi_get_str(vpiName, keyword), nullptr) << name;
  }
}

TEST_F(TypespecsOfARun, OnlyAnAssociativeArrayReachesAnIndexTypespec) {
  Run("module top;\n"
      "  typedef int aa_t [string]; typedef int q_t "
      "[$];\n"
      "  typedef int f_t [4]; typedef int r_t [3:0];\n"
      "  typedef struct { int a; } s_t; typedef int "
      "i_t;\n"
      "endmodule\n");
  vpiHandle top = By("top");
  EXPECT_EQ(
      KindOf(vpi_handle(vpiIndexTypespec, Named(vpiTypedef, top, "aa_t"))),
      vpiStringTypespec);
  for (const char* name : {"q_t", "f_t", "r_t", "s_t", "i_t"}) {
    vpiHandle typespec = Named(vpiTypedef, top, name);
    ASSERT_NE(typespec, nullptr) << name;
    EXPECT_EQ(vpi_handle(vpiIndexTypespec, typespec), nullptr) << name;
  }
}

TEST_F(TypespecsOfARun, SeveralPackedDimensionsUnwindOneAtATime) {
  Run("module top; typedef logic [3:0][1:0] lt; "
      "typedef bit [2:0][4:6] bt;\n"
      "endmodule\n");
  vpiHandle top = By("top");
  const std::pair<const char*, int> kTypedefs[] = {{"lt", vpiLogicTypespec},
                                                   {"bt", vpiBitTypespec}};
  const std::vector<int> kInnerBounds[] = {{1, 0}, {4, 6}};
  for (int i = 0; i < 2; ++i) {
    const auto& [name, kind] = kTypedefs[i];
    vpiHandle outer = Named(vpiTypedef, top, name);
    ASSERT_NE(outer, nullptr) << name;
    vpiHandle inner = vpi_handle(vpiElemTypespec, outer);
    ASSERT_NE(inner, nullptr) << name;
    EXPECT_EQ(vpi_get(vpiType, inner), kind) << name;
    EXPECT_EQ(vpi_get_str(vpiName, inner), nullptr) << name;
    EXPECT_EQ(BoundsOf(inner), kInnerBounds[i]) << name;
    vpiHandle scalar = vpi_handle(vpiElemTypespec, inner);
    ASSERT_NE(scalar, nullptr) << name;
    EXPECT_EQ(vpi_get(vpiType, scalar), kind) << name;
    EXPECT_TRUE(SizesOfRanges(scalar).empty()) << name;
    EXPECT_EQ(vpi_handle(vpiElemTypespec, scalar), nullptr) << name;
  }
}

TEST_F(TypespecsOfARun, ARangelessLogicTypespecHasNoElement) {
  Run("module top; typedef logic l_t; typedef logic "
      "[1:0] w_t; endmodule\n");
  vpiHandle top = By("top");
  EXPECT_EQ(vpi_handle(vpiElemTypespec, Named(vpiTypedef, top, "l_t")),
            nullptr);
  EXPECT_EQ(KindOf(vpi_handle(vpiElemTypespec, Named(vpiTypedef, top, "w_t"))),
            vpiLogicTypespec);
}

TEST_F(TypespecsOfARun, AUnionTypespecHasNoElement) {
  Run("module top; typedef union { int i; bit b; } "
      "u_t;\n"
      "  typedef union packed { bit [3:0] a; bit [3:0] "
      "b; } pu_t;\n"
      "endmodule\n");
  vpiHandle top = By("top");
  for (const char* name : {"u_t", "pu_t"}) {
    vpiHandle typespec = Named(vpiTypedef, top, name);
    ASSERT_NE(typespec, nullptr) << name;
    EXPECT_EQ(vpi_handle(vpiElemTypespec, typespec), nullptr) << name;
  }
}

TEST_F(TypespecsOfARun, TwoUnpackedDimensionsUnwindOneAtATime) {
  Run("module top; typedef int t [2][3]; endmodule\n");
  vpiHandle t = Named(vpiTypedef, By("top"), "t");
  ASSERT_NE(t, nullptr);
  EXPECT_EQ(SizesOfRanges(t), (std::vector<int>{2, 3}));
  vpiHandle row = vpi_handle(vpiElemTypespec, t);
  ASSERT_NE(row, nullptr);
  EXPECT_EQ(vpi_get(vpiType, row), vpiArrayTypespec);
  EXPECT_EQ(vpi_get_str(vpiName, row), nullptr);
  EXPECT_EQ(BoundsOf(row), (std::vector<int>{0, 2}));
  EXPECT_EQ(KindOf(vpi_handle(vpiElemTypespec, row)), vpiIntTypespec);
}

TEST_F(TypespecsOfARun, ADynamicLeftmostDimensionUnwindsLikeAFixedOne) {
  Run("module top; typedef int dm_t [][3]; "
      "endmodule\n");
  vpiHandle dm = Named(vpiTypedef, By("top"), "dm_t");
  ASSERT_NE(dm, nullptr);
  EXPECT_EQ(vpi_get(vpiArrayType, dm), vpiDynamicArray);
  vpiHandle row = vpi_handle(vpiElemTypespec, dm);
  ASSERT_NE(row, nullptr);
  EXPECT_EQ(vpi_get(vpiType, row), vpiArrayTypespec);
  EXPECT_EQ(vpi_get(vpiArrayType, row), vpiStaticArray);
  EXPECT_EQ(BoundsOf(row), (std::vector<int>{0, 2}));
  EXPECT_EQ(KindOf(vpi_handle(vpiElemTypespec, row)), vpiIntTypespec);
}

TEST_F(TypespecsOfARun, APackedArrayOfAPackedUnionUnwindsToTheUnion) {
  Run("module top;\n"
      "  typedef union packed { bit [3:0] a; bit [3:0] "
      "b; } u_t;\n"
      "  typedef u_t [1:0] ua_t;\n"
      "endmodule\n");
  vpiHandle top = By("top");
  vpiHandle ua = Named(vpiTypedef, top, "ua_t");
  ASSERT_NE(ua, nullptr);
  EXPECT_EQ(vpi_get(vpiType, ua), vpiPackedArrayTypespec);
  EXPECT_TRUE(
      Same(vpi_handle(vpiElemTypespec, ua), Named(vpiTypedef, top, "u_t")));
}

TEST_F(TypespecsOfARun, ALogicTypespecIsAVectorOnlyWithARange) {
  Run("module top; typedef logic [7:0] b_t; typedef "
      "logic l_t; endmodule\n");
  vpiHandle top = By("top");
  vpiHandle b = Named(vpiTypedef, top, "b_t");
  vpiHandle l = Named(vpiTypedef, top, "l_t");
  ASSERT_NE(b, nullptr);
  ASSERT_NE(l, nullptr);
  EXPECT_EQ(vpi_get(vpiVector, b), 1);
  vpiHandle bit = vpi_handle(vpiElemTypespec, b);
  ASSERT_NE(bit, nullptr);
  EXPECT_EQ(vpi_get(vpiVector, bit), 0);
  EXPECT_EQ(vpi_get(vpiVector, l), 0);
}

constexpr const char* kUnboundedArrays =
    "module top; typedef int my_t;\n"
    "  typedef int aa_t [string]; typedef bit ab_t "
    "[my_t];\n"
    "  typedef byte aw_t [*]; typedef int q_t [$]; "
    "typedef int da_t [];\n"
    "endmodule\n";

TEST_F(TypespecsOfARun, AnAssociativeOrQueueTypespecIteratesOneEmptyRange) {
  Run(kUnboundedArrays);
  vpiHandle top = By("top");
  for (const char* name : {"aa_t", "ab_t", "aw_t", "q_t"}) {
    vpiHandle typespec = Named(vpiTypedef, top, name);
    ASSERT_NE(typespec, nullptr) << name;
    EXPECT_EQ(SizesOfRanges(typespec), (std::vector<int>{0})) << name;
  }
}

TEST_F(TypespecsOfARun, AnUnboundedArrayTypespecHasNoBounds) {
  Run(kUnboundedArrays);
  vpiHandle top = By("top");
  for (const char* name : {"aa_t", "ab_t", "aw_t", "q_t", "da_t"}) {
    vpiHandle typespec = Named(vpiTypedef, top, name);
    ASSERT_NE(typespec, nullptr) << name;
    EXPECT_EQ(vpi_handle(vpiLeftRange, typespec), nullptr) << name;
    EXPECT_EQ(vpi_handle(vpiRightRange, typespec), nullptr) << name;
  }
}

TEST_F(TypespecsOfARun, AMixedArrayTypespecRangesEachDimension) {
  Run("module top; typedef int dm_t [][3]; typedef int "
      "qm_t [3][$];\n"
      "endmodule\n");
  vpiHandle top = By("top");
  vpiHandle dm = Named(vpiTypedef, top, "dm_t");
  vpiHandle qm = Named(vpiTypedef, top, "qm_t");
  ASSERT_NE(dm, nullptr);
  ASSERT_NE(qm, nullptr);
  EXPECT_EQ(SizesOfRanges(dm), (std::vector<int>{0, 3}));
  EXPECT_TRUE(LeftmostBoundsOf(dm).empty());
  EXPECT_EQ(SizesOfRanges(qm), (std::vector<int>{3, 0}));
  EXPECT_EQ(LeftmostBoundsOf(qm), (std::vector<int>{0, 2}));
}

constexpr const char* kDetailEightsArrays =
    "module top;\n"
    "  typedef struct packed { int i1; bit bvec; } "
    "[1:3] parrtype;\n"
    "  typedef parrtype [2:1] parrtype2;\n"
    "  typedef parrtype2 unparrtype [6:4];\n"
    "  unparrtype arr [3:0];\n"
    "  typedef logic [3:0][7:0] w_t;\n"
    "endmodule\n";

TEST_F(TypespecsOfARun, APackedArrayTypespecsBoundsAreItsLeftmostDimension) {
  Run(kDetailEightsArrays);
  vpiHandle parr2 = Named(vpiTypedef, By("top"), "parrtype2");
  ASSERT_NE(parr2, nullptr);
  EXPECT_EQ(LeftmostBoundsOf(parr2), (std::vector<int>{2, 1}));
}

TEST_F(TypespecsOfARun, ALogicTypespecsBoundsAreItsLeftmostDimension) {
  Run(kDetailEightsArrays);
  vpiHandle w = Named(vpiTypedef, By("top"), "w_t");
  ASSERT_NE(w, nullptr);
  EXPECT_EQ(LeftmostBoundsOf(w), (std::vector<int>{3, 0}));
}

TEST_F(TypespecsOfARun, AnArrayTypespecsBoundsAreItsLeftmostUnpackedDimension) {
  Run(kDetailEightsArrays);
  vpiHandle arr = vpi_handle(vpiTypespec, By("top.arr"));
  ASSERT_NE(arr, nullptr);
  EXPECT_EQ(LeftmostBoundsOf(arr), (std::vector<int>{3, 0}));
  EXPECT_EQ(LeftmostBoundsOf(Named(vpiTypedef, By("top"), "unparrtype")),
            (std::vector<int>{6, 4}));
}

TEST_F(TypespecsOfARun, AStructTypespecIsNeitherTaggedNorSoft) {
  Run("module top; typedef struct packed { bit a; bit "
      "[2:0] b; } ps_t;\n"
      "  typedef struct { int a; } us_t; endmodule\n");
  vpiHandle top = By("top");
  for (const char* name : {"ps_t", "us_t"}) {
    vpiHandle typespec = Named(vpiTypedef, top, name);
    ASSERT_NE(typespec, nullptr) << name;
    EXPECT_EQ(vpi_get(vpiTagged, typespec), 0) << name;
    EXPECT_EQ(vpi_get(vpiSoft, typespec), 0) << name;
  }
}

TEST_F(TypespecsOfARun, APlainUnionTypespecIsNotPackedTaggedOrSoft) {
  Run("module top; typedef union { int i; bit b; } "
      "u_t;\n"
      "  typedef union tagged { int i; bit b; } tu_t; "
      "endmodule\n");
  vpiHandle u = Named(vpiTypedef, By("top"), "u_t");
  ASSERT_NE(u, nullptr);
  EXPECT_EQ(vpi_get(vpiPacked, u), 0);
  EXPECT_EQ(vpi_get(vpiTagged, u), 0);
  EXPECT_EQ(vpi_get(vpiSoft, u), 0);
  EXPECT_EQ(vpi_get(vpiTagged, Named(vpiTypedef, By("top"), "tu_t")), 1);
}

TEST_F(TypespecsOfARun, APackedOrUnionMemberReachesNoDefault) {
  Run("module top;\n"
      "  typedef struct packed { bit [3:0] a; bit b; } "
      "ps_t;\n"
      "  typedef union { int i; bit b; } u_t;\n"
      "  typedef union packed { bit [3:0] x; bit [3:0] "
      "y; } pu_t;\n"
      "  typedef struct { int d = 7; } us_t;\n"
      "endmodule\n");
  vpiHandle top = By("top");
  for (const char* name : {"ps_t", "u_t", "pu_t"}) {
    vpiHandle typespec = Named(vpiTypedef, top, name);
    ASSERT_NE(typespec, nullptr) << name;
    std::vector<vpiHandle> members = ObjectsOf(vpiTypespecMember, typespec);
    EXPECT_EQ(members.size(), 2u) << name;
    for (vpiHandle member : members) {
      EXPECT_EQ(vpi_handle(vpiExpr, member), nullptr) << name;
    }
  }
  vpiHandle d = Named(vpiTypespecMember, Named(vpiTypedef, top, "us_t"), "d");
  ASSERT_NE(d, nullptr);
  vpiHandle value = vpi_handle(vpiExpr, d);
  ASSERT_NE(value, nullptr);
  EXPECT_EQ(IntegerOf(value), 7);
}

TEST_F(TypespecsOfARun, AnUntaggedUnionsMembersReachTheirTypes) {
  Run("module top; typedef bit [3:0] nib_t;\n"
      "  typedef union packed { nib_t n; bit [3:0] b; "
      "} pu_t;\n"
      "  typedef union { int i; nib_t n; shortreal r; "
      "} uu_t;\n"
      "endmodule\n");
  vpiHandle top = By("top");
  vpiHandle nib = Named(vpiTypedef, top, "nib_t");
  vpiHandle pu = Named(vpiTypedef, top, "pu_t");
  vpiHandle uu = Named(vpiTypedef, top, "uu_t");
  ASSERT_NE(pu, nullptr);
  ASSERT_NE(uu, nullptr);
  EXPECT_EQ(NamesOf(vpiTypespecMember, pu),
            (std::vector<std::string>{"b", "n"}));
  EXPECT_TRUE(Same(MemberType(pu, "n"), nib));
  vpiHandle b = MemberType(pu, "b");
  EXPECT_EQ(KindOf(b), vpiBitTypespec);
  EXPECT_EQ(BoundsOf(b), (std::vector<int>{3, 0}));
  EXPECT_EQ(NamesOf(vpiTypespecMember, uu),
            (std::vector<std::string>{"i", "n", "r"}));
  EXPECT_EQ(KindOf(MemberType(uu, "i")), vpiIntTypespec);
  EXPECT_TRUE(Same(MemberType(uu, "n"), nib));
  EXPECT_EQ(KindOf(MemberType(uu, "r")), vpiShortRealTypespec);
}

TEST_F(TypespecsOfARun, AClassTypedefOfATypedefReachesIt) {
  Run("module top;\n"
      "  class C; typedef logic [3:0] nib_t; typedef "
      "nib_t half_t; endclass\n"
      "endmodule\n");
  vpiHandle c = Named(vpiClassDefn, By("top"), "C");
  ASSERT_NE(c, nullptr);
  vpiHandle half = Named(vpiTypedef, c, "half_t");
  vpiHandle nib = Named(vpiTypedef, c, "nib_t");
  ASSERT_NE(half, nullptr);
  ASSERT_NE(nib, nullptr);
  EXPECT_EQ(vpi_get(vpiType, half), vpiLogicTypespec);
  EXPECT_TRUE(Same(vpi_handle(vpiTypedefAlias, half), nib));
  EXPECT_EQ(vpi_handle(vpiTypedefAlias, nib), nullptr);
}

TEST_F(TypespecsOfARun, AnInterfaceTypedefOfATypedefReachesIt) {
  Run("interface ifc; typedef logic [3:0] nib_t; "
      "typedef nib_t half_t;\n"
      "  nib_t n; half_t h; endinterface\n"
      "module top; ifc i(); endmodule\n");
  ExpectAliasChainThroughVariables("top.i");
}

TEST_F(TypespecsOfARun, AProgramTypedefOfATypedefReachesIt) {
  Run("program prg; typedef logic [3:0] nib_t; typedef "
      "nib_t half_t;\n"
      "  nib_t n; half_t h; endprogram\n"
      "module top; prg g(); endmodule\n");
  ExpectAliasChainThroughVariables("top.g");
}

TEST_F(TypespecsOfARun, AnEnumBaseNamedByATypedefIsThatTypedef) {
  Run("module top; typedef bit [2:0] b3_t; typedef "
      "enum b3_t {A, B} e_t;\n"
      "  typedef bit b_t; typedef enum b_t [1:0] {P, "
      "Q} f_t;\n"
      "endmodule\n");
  vpiHandle top = By("top");
  vpiHandle e = Named(vpiTypedef, top, "e_t");
  ASSERT_NE(e, nullptr);
  EXPECT_TRUE(
      Same(vpi_handle(vpiBaseTypespec, e), Named(vpiTypedef, top, "b3_t")));
  vpiHandle f = Named(vpiTypedef, top, "f_t");
  ASSERT_NE(f, nullptr);
  vpiHandle base = vpi_handle(vpiBaseTypespec, f);
  EXPECT_EQ(KindOf(base), vpiBitTypespec);
  EXPECT_EQ(BoundsOf(base), (std::vector<int>{1, 0}));
}

TEST_F(TypespecsOfARun, AnEnumOfAKeywordBaseReachesThatKeywordsTypespec) {
  Run("module top;\n"
      "  typedef enum byte {A} by_e; typedef enum "
      "shortint {B} si_e;\n"
      "  typedef enum longint {C} li_e; typedef enum "
      "integer {D} ig_e;\n"
      "  typedef enum logic [3:0] {E} lo_e; typedef "
      "enum bit {F} bi_e;\n"
      "  enum logic [1:0] {G, H} v;\n"
      "endmodule\n");
  vpiHandle top = By("top");
  const std::pair<const char*, int> kBases[] = {
      {"by_e", vpiByteTypespec},    {"si_e", vpiShortIntTypespec},
      {"li_e", vpiLongIntTypespec}, {"ig_e", vpiIntegerTypespec},
      {"lo_e", vpiLogicTypespec},   {"bi_e", vpiBitTypespec},
  };
  for (const auto& [name, kind] : kBases) {
    EXPECT_EQ(KindOf(vpi_handle(vpiBaseTypespec, Named(vpiTypedef, top, name))),
              kind)
        << name;
  }
  EXPECT_EQ(
      BoundsOf(vpi_handle(vpiBaseTypespec, Named(vpiTypedef, top, "lo_e"))),
      (std::vector<int>{3, 0}));
  vpiHandle in_place =
      vpi_handle(vpiBaseTypespec, vpi_handle(vpiTypespec, By("top.v")));
  EXPECT_EQ(KindOf(in_place), vpiLogicTypespec);
  EXPECT_EQ(BoundsOf(in_place), (std::vector<int>{1, 0}));
}

TEST_F(TypespecsOfARun,
       DISABLED_AnArrayVarOfAnUnpackedArrayTypedefReachesItByName) {
  Run("interface SBus; logic a; modport phy(input a); endinterface\n"
      "package pk; typedef byte pa_t [2]; endpackage\n"
      "typedef logic [3:0] ua_t [1:2];\n"
      "interface ifc; typedef int ia_t [3]; ia_t ia; endinterface\n"
      "program prg; typedef bit pg_t [2]; pg_t pg; endprogram\n"
      "module top;\n"
      "  typedef logic [3:0] la_t [1:2];\n"
      "  typedef virtual SBus.phy SBphy [1:4];\n"
      "  typedef logic [3:0] nib_t;\n"
      "  la_t la; ua_t ua; pk::pa_t pa; SBphy arr; nib_t n;\n"
      "  ifc i(); prg p();\n"
      "endmodule\n");
  Names names;
  for (const char* var : {"top.la", "top.ua", "top.pa", "top.arr", "top.i.ia",
                          "top.p.pg", "top.n"}) {
    vpiHandle typespec = vpi_handle(vpiTypespec, By(var));
    const char* name =
        typespec == nullptr ? nullptr : vpi_get_str(vpiName, typespec);
    names.emplace_back(name == nullptr ? "<null>" : name);
  }
  EXPECT_EQ(names,
            (Names{"la_t", "ua_t", "pa_t", "SBphy", "ia_t", "pg_t", "nib_t"}));
  EXPECT_EQ(KindOf(vpi_handle(vpiTypespec, By("top.la"))), vpiArrayTypespec);
}

}  // namespace
}  // namespace delta
