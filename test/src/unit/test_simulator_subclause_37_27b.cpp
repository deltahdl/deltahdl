#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "fixture_vpi_named_events.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

constexpr const char* kEventsOfEveryPlace =
    "event ue; event ua [1:3]; event um [0:1][3:5];\n"
    "package pkg; event pe; event pa [1:3]; event pm [0:1][3:5]; endpackage\n"
    "interface ifc; event ie; event ia [1:3]; event im [0:1][3:5];\n"
    "endinterface\n"
    "program prg; event qe; event qa [1:3]; event qm [0:1][3:5]; endprogram\n"
    "module top;\n"
    "  event me; event ma [1:3]; event mm [0:1][3:5]; int av [2];\n"
    "  ifc i0(); prg p0();\n"
    "  task t; event te; event ta [1:3]; event tm [0:1][3:5]; endtask\n"
    "  function void f; event fe; event fa [1:3]; event fm [0:1][3:5];\n"
    "  endfunction\n"
    "  if (1) begin : g event ge; event ga [1:3]; event gm [0:1][3:5]; end\n"
    "  initial begin : nb event be; event ba [1:3]; event bm [0:1][3:5]; end\n"
    "  initial fork : nf event ke; event ka [1:3]; event km [0:1][3:5]; join\n"
    "endmodule\n";

constexpr Place kInstancesAndGenerateBlock[] = {kModule, kInterface, kProgram,
                                                kGenerate};
constexpr Place kPackageSubroutinesBlocksAndUnit[] = {
    kPackage, kTask, kFunction, kBlock, kFork, kUnit};
constexpr Place kInstances[] = {kModule, kInterface, kProgram};
constexpr Place kInstancesSubroutinesAndGenerateBlock[] = {
    kModule, kInterface, kProgram, kTask, kFunction, kGenerate};
constexpr Place kPackageBlocksAndUnit[] = {kPackage, kBlock, kFork, kUnit};

TEST_F(EventsOfEveryPlace, EveryPlacesEventsAndEventArraysHaveTheirKinds) {
  Run(kEventsOfEveryPlace);
  ForEach(kEveryPlace, ExpectKinds);
}

TEST_F(EventsOfEveryPlace, AnInstanceOrGenerateBlocksArrayElementIsAnEvent) {
  Run(kEventsOfEveryPlace);
  ForEach(kInstancesAndGenerateBlock, ExpectElementKinds);
}

TEST_F(EventsOfEveryPlace,
       DISABLED_APackageSubroutineBlockOrTheUnitsArrayElementIsAnEvent) {
  Run(kEventsOfEveryPlace);
  ForEach(kPackageSubroutinesBlocksAndUnit, ExpectElementKinds);
}

TEST_F(EventsOfEveryPlace, AnInstanceOrGenerateBlocksEventHasTheEventTypespec) {
  Run(kEventsOfEveryPlace);
  ForEach(kInstancesAndGenerateBlock, ExpectEventTypespec);
}

TEST_F(EventsOfEveryPlace,
       DISABLED_APackageSubroutineBlockOrTheUnitsEventHasTheEventTypespec) {
  Run(kEventsOfEveryPlace);
  ForEach(kPackageSubroutinesBlocksAndUnit, ExpectEventTypespec);
}

TEST_F(EventsOfEveryPlace, DISABLED_AnArrayElementHasTheEventTypespec) {
  Run(kEventsOfEveryPlace);
  ForEach(kEveryPlace, ExpectElementTypespecs);
}

TEST_F(EventsOfEveryPlace, AnInstanceOrGenerateBlocksEventArrayIsOfEvents) {
  Run(kEventsOfEveryPlace);
  ForEach(kInstancesAndGenerateBlock, ExpectArraysOfEvents);
}

TEST_F(EventsOfEveryPlace,
       DISABLED_APackageSubroutineBlockOrTheUnitsEventArrayIsOfEvents) {
  Run(kEventsOfEveryPlace);
  ForEach(kPackageSubroutinesBlocksAndUnit, ExpectArraysOfEvents);
}

TEST_F(EventsOfEveryPlace, EveryPlacesEventHasItsNameAndFullName) {
  Run(kEventsOfEveryPlace);
  ForEach(kEveryPlace, [](const Place& p) {
    EXPECT_EQ(Str(vpiName, EventIn(p)), NameIn(p, 'e'));
    EXPECT_EQ(Str(vpiFullName, EventIn(p)), p.prefix + NameIn(p, 'e'));
  });
}

TEST_F(EventsOfEveryPlace, AnInstancesArrayElementsNameCarriesItsIndices) {
  Run(kEventsOfEveryPlace);
  ForEach(kInstances, ExpectElementNames);
}

TEST_F(EventsOfEveryPlace,
       DISABLED_AGenerateBlocksArrayElementsNameCarriesItsIndices) {
  Run(kEventsOfEveryPlace);
  ExpectElementNames(kGenerate);
}

TEST_F(
    EventsOfEveryPlace,
    DISABLED_APackageSubroutineBlockOrTheUnitsArrayElementsNameCarriesItsIndices) {
  Run(kEventsOfEveryPlace);
  ForEach(kPackageSubroutinesBlocksAndUnit, ExpectElementNames);
}

TEST_F(EventsOfEveryPlace, EveryPlacesEventArrayHasItsNameAndFullName) {
  Run(kEventsOfEveryPlace);
  ForEach(kEveryPlace, [](const Place& p) {
    for (const char kKind : {'a', 'm'}) {
      vpiHandle array = Named(vpiNamedEventArray, ScopeOf(p), NameIn(p, kKind));
      EXPECT_EQ(Str(vpiName, array), NameIn(p, kKind));
      EXPECT_EQ(Str(vpiFullName, array), p.prefix + NameIn(p, kKind));
    }
  });
}

TEST_F(EventsOfEveryPlace, EveryPlacesEventReachesItsInstanceAndModule) {
  Run(kEventsOfEveryPlace);
  ForEach(kEveryPlace, [](const Place& p) {
    vpiHandle event = EventIn(p);
    ASSERT_NE(event, nullptr);
    EXPECT_EQ(Reached(vpiInstance, event), VpiObjectOf(InstanceOf(p)));
    EXPECT_EQ(Reached(vpiModule, event), VpiObjectOf(ModuleOf(p)));
  });
}

TEST_F(EventsOfEveryPlace, DISABLED_EveryPlacesEventReachesItsScope) {
  Run(kEventsOfEveryPlace);
  ForEach(kEveryPlace, [](const Place& p) {
    EXPECT_EQ(Reached(vpiScope, EventIn(p)), VpiObjectOf(ScopeOf(p)));
  });
}

TEST_F(EventsOfEveryPlace,
       AnInstanceOrGenerateBlocksArrayElementReachesItsInstanceAndModule) {
  Run(kEventsOfEveryPlace);
  ForEach(kInstancesAndGenerateBlock, ExpectElementInstanceAndModule);
}

TEST_F(
    EventsOfEveryPlace,
    DISABLED_APackageSubroutineBlockOrTheUnitsArrayElementReachesItsInstanceAndModule) {
  Run(kEventsOfEveryPlace);
  ForEach(kPackageSubroutinesBlocksAndUnit, ExpectElementInstanceAndModule);
}

TEST_F(EventsOfEveryPlace, DISABLED_EveryPlacesArrayElementReachesItsScope) {
  Run(kEventsOfEveryPlace);
  ForEach(kEveryPlace, [](const Place& p) {
    EXPECT_EQ(Reached(vpiScope, ElementIn(p)), VpiObjectOf(ScopeOf(p)));
    EXPECT_EQ(Reached(vpiScope, CellIn(p, 1, 4)), VpiObjectOf(ScopeOf(p)));
  });
}

TEST_F(EventsOfEveryPlace, EveryPlacesEventArrayReachesItsInstanceAndModule) {
  Run(kEventsOfEveryPlace);
  ForEach(kEveryPlace, [](const Place& p) {
    for (vpiHandle array : {ArrayIn(p), GridIn(p)}) {
      ASSERT_NE(array, nullptr);
      EXPECT_EQ(Reached(vpiInstance, array), VpiObjectOf(InstanceOf(p)));
      EXPECT_EQ(Reached(vpiModule, array), VpiObjectOf(ModuleOf(p)));
    }
  });
}

TEST_F(EventsOfEveryPlace, EveryPlaceIteratesOnlyItsOwnEventsAndEventArrays) {
  Run(kEventsOfEveryPlace);
  ForEach(kEveryPlace, [](const Place& p) {
    EXPECT_EQ(NamesOf(vpiNamedEvent, ScopeOf(p)),
              std::vector<std::string>{NameIn(p, 'e')});
    EXPECT_EQ(NamesOf(vpiNamedEventArray, ScopeOf(p)),
              (std::vector<std::string>{NameIn(p, 'a'), NameIn(p, 'm')}));
  });
}

TEST_F(EventsOfEveryPlace,
       AnInstanceOrGenerateBlocksEventArrayIteratesItsElements) {
  Run(kEventsOfEveryPlace);
  ForEach(kInstancesAndGenerateBlock, ExpectRowIterated);
}

TEST_F(
    EventsOfEveryPlace,
    DISABLED_APackageSubroutineBlockOrTheUnitsEventArrayIteratesItsElements) {
  Run(kEventsOfEveryPlace);
  ForEach(kPackageSubroutinesBlocksAndUnit, ExpectRowIterated);
}

TEST_F(EventsOfEveryPlace,
       DISABLED_EveryPlacesTwoDimensionalEventArrayIteratesEveryElement) {
  Run(kEventsOfEveryPlace);
  ForEach(kEveryPlace, ExpectGridIterated);
}

TEST_F(EventsOfEveryPlace,
       AnInstanceOrGenerateBlocksArrayElementIsAnArrayMember) {
  Run(kEventsOfEveryPlace);
  ForEach(kInstancesAndGenerateBlock, ExpectElementsAreArrayMembers);
}

TEST_F(EventsOfEveryPlace,
       DISABLED_APackageSubroutineBlockOrTheUnitsArrayElementIsAnArrayMember) {
  Run(kEventsOfEveryPlace);
  ForEach(kPackageSubroutinesBlocksAndUnit, ExpectElementsAreArrayMembers);
}

TEST_F(EventsOfEveryPlace, EveryPlacesScalarEventIsNoArrayMember) {
  Run(kEventsOfEveryPlace);
  ForEach(kEveryPlace, [](const Place& p) {
    EXPECT_EQ(Flag(vpiArrayMember, EventIn(p)), 0);
    EXPECT_EQ(Flag(vpiArray, EventIn(p)), 0);
  });
}

TEST_F(EventsOfEveryPlace,
       DISABLED_AnArrayElementIsAnArrayMemberByTheDeprecatedProperty) {
  Run(kEventsOfEveryPlace);
  ForEach(kEveryPlace, ExpectElementsFlaggedAsArrays);
}

TEST_F(EventsOfEveryPlace,
       AnInstanceOrGenerateBlocksArrayElementsIndicesRunOutward) {
  Run(kEventsOfEveryPlace);
  ForEach(kInstancesAndGenerateBlock, ExpectElementIndices);
}

TEST_F(
    EventsOfEveryPlace,
    DISABLED_APackageSubroutineBlockOrTheUnitsArrayElementsIndicesRunOutward) {
  Run(kEventsOfEveryPlace);
  ForEach(kPackageSubroutinesBlocksAndUnit, ExpectElementIndices);
}

TEST_F(EventsOfEveryPlace, EveryPlacesScalarEventHasNoIndex) {
  Run(kEventsOfEveryPlace);
  ForEach(kEveryPlace, [](const Place& p) {
    vpiHandle event = EventIn(p);
    ASSERT_NE(event, nullptr);
    EXPECT_EQ(vpi_iterate(vpiIndex, event), nullptr);
  });
}

TEST_F(EventsOfEveryPlace,
       AnInstanceSubroutineOrGenerateBlocksEventArrayRangesRunLeftToRight) {
  Run(kEventsOfEveryPlace);
  ForEach(kInstancesSubroutinesAndGenerateBlock, ExpectRanges);
}

TEST_F(EventsOfEveryPlace,
       DISABLED_APackageBlockOrTheUnitsEventArrayRangesRunLeftToRight) {
  Run(kEventsOfEveryPlace);
  ForEach(kPackageBlocksAndUnit, ExpectRanges);
}

TEST_F(EventsOfEveryPlace,
       AnInstanceOrGenerateBlocksEventArrayIsIndexedByItsIndices) {
  Run(kEventsOfEveryPlace);
  ForEach(kInstancesAndGenerateBlock, ExpectIndexedAccess);
}

TEST_F(
    EventsOfEveryPlace,
    DISABLED_APackageSubroutineBlockOrTheUnitsEventArrayIsIndexedByItsIndices) {
  Run(kEventsOfEveryPlace);
  ForEach(kPackageSubroutinesBlocksAndUnit, ExpectIndexedAccess);
}

TEST_F(EventsOfEveryPlace,
       DISABLED_ATwoDimensionalArraysElementHasTheArrayAsParent) {
  Run(kEventsOfEveryPlace);
  ForEach(kEveryPlace, ExpectCellParent);
}

TEST_F(EventsOfEveryPlace, EveryPlacesEventAndEventArrayAreStatic) {
  Run(kEventsOfEveryPlace);
  ForEach(kEveryPlace, ExpectStaticDeclarations);
}

TEST_F(EventsOfEveryPlace, AnInstanceOrGenerateBlocksArrayElementIsStatic) {
  Run(kEventsOfEveryPlace);
  ForEach(kInstancesAndGenerateBlock, ExpectStaticElements);
}

TEST_F(EventsOfEveryPlace,
       DISABLED_APackageSubroutineBlockOrTheUnitsArrayElementIsStatic) {
  Run(kEventsOfEveryPlace);
  ForEach(kPackageSubroutinesBlocksAndUnit, ExpectStaticElements);
}

TEST_F(EventsOfEveryPlace, AnEventReachesItsDynamicWaitersAsThreads) {
  Run("module top; event e;\n"
      "  initial @e;\n"
      "  initial begin fork @e; join_none end\n"
      "  initial begin fork @e; #5; join_any end\n"
      "endmodule\n");
  const std::vector<vpiHandle> kWaiters =
      ObjectsOf(vpiWaitingProcesses, By("top.e"));
  EXPECT_EQ(kWaiters.size(), 3U);
  for (vpiHandle waiter : kWaiters) EXPECT_EQ(KindOf(waiter), vpiThread);
}

constexpr const char* kLifetimes =
    "module top; event se; event sa [1:3];\n"
    "  task automatic at; event ae; event aa [1:3]; event am [0:1][3:5];\n"
    "    static event ks;\n"
    "  endtask\n"
    "  function automatic int af; event fe; event fa [1:3]; return 0;\n"
    "  endfunction\n"
    "  task st; automatic event ka; endtask\n"
    "  class C; event ce; static event ke; endclass\n"
    "  C c = new;\n"
    "endmodule\n";

TEST_F(EventsOfEveryPlace, AnEventsLifetimeFollowsWhereItIsDeclared) {
  Run(kLifetimes);
  vpiHandle at = Named(vpiTaskFunc, By("top"), "at");
  vpiHandle af = Named(vpiTaskFunc, By("top"), "af");
  vpiHandle st = Named(vpiTaskFunc, By("top"), "st");
  vpiHandle obj = vpi_handle(vpiClassObj, By("top.c"));
  ASSERT_NE(at, nullptr);
  ASSERT_NE(af, nullptr);
  ASSERT_NE(st, nullptr);
  ASSERT_NE(obj, nullptr);
  struct Case {
    vpiHandle event;
    int automatic;
    int scheme;
  };
  const Case kCases[] = {
      {By("top.se"), 0, vpiOtherScheme},
      {By("top.sa"), 0, vpiOtherScheme},
      {Named(vpiNamedEvent, at, "ae"), 1, vpiAutomaticScheme},
      {Named(vpiNamedEventArray, at, "aa"), 1, vpiAutomaticScheme},
      {Named(vpiNamedEventArray, at, "am"), 1, vpiAutomaticScheme},
      {Named(vpiNamedEvent, at, "ks"), 0, vpiOtherScheme},
      {Named(vpiNamedEvent, af, "fe"), 1, vpiAutomaticScheme},
      {Named(vpiNamedEventArray, af, "fa"), 1, vpiAutomaticScheme},
      {Named(vpiNamedEvent, st, "ka"), 1, vpiAutomaticScheme},
      {Named(vpiNamedEvent, obj, "ce"), 1, vpiDynamicScheme},
      {Named(vpiNamedEvent, obj, "ke"), 0, vpiOtherScheme},
  };
  for (const Case& c : kCases) {
    SCOPED_TRACE(Str(vpiName, c.event));
    EXPECT_EQ(Flag(vpiAutomatic, c.event), c.automatic);
    EXPECT_EQ(Flag(vpiAllocScheme, c.event), c.scheme);
  }
}

TEST_F(EventsOfEveryPlace,
       DISABLED_AnAutomaticSubroutinesArrayElementIsAutomatic) {
  Run(kLifetimes);
  vpiHandle at = Named(vpiTaskFunc, By("top"), "at");
  vpiHandle af = Named(vpiTaskFunc, By("top"), "af");
  ASSERT_NE(at, nullptr);
  ASSERT_NE(af, nullptr);
  vpiHandle aa = Named(vpiNamedEventArray, at, "aa");
  vpiHandle am = Named(vpiNamedEventArray, at, "am");
  vpiHandle fa = Named(vpiNamedEventArray, af, "fa");
  ASSERT_NE(aa, nullptr);
  ASSERT_NE(am, nullptr);
  ASSERT_NE(fa, nullptr);
  PLI_INT32 cell[] = {1, 4};
  ExpectLifetime(vpi_handle_by_index(aa, 2), 1, vpiAutomaticScheme);
  ExpectLifetime(vpi_handle_by_multi_index(am, 2, cell), 1, vpiAutomaticScheme);
  ExpectLifetime(vpi_handle_by_index(fa, 2), 1, vpiAutomaticScheme);
}

constexpr const char* kWaitersOfEveryPlace =
    "event ue; event ua [1:3]; event um [0:1][3:5];\n"
    "package pkg; event pe; event pa [1:3]; event pm [0:1][3:5]; endpackage\n"
    "interface ifc; event ie; event ia [1:3]; event im [0:1][3:5]; int hits;\n"
    "  initial begin @ie; hits |= 1; end\n"
    "  initial begin @(ia[2]); hits |= 2; end\n"
    "  initial begin @(im[1][4]); hits |= 4; end\n"
    "endinterface\n"
    "program prg; event qe; event qa [1:3]; event qm [0:1][3:5]; int hits;\n"
    "  initial begin @qe; hits |= 1; end\n"
    "  initial begin @(qa[2]); hits |= 2; end\n"
    "  initial begin @(qm[1][4]); hits |= 4; end\n"
    "endprogram\n"
    "module top;\n"
    "  event me; event ma [1:3]; event mm [0:1][3:5];\n"
    "  int hits; int late; int fired;\n"
    "  ifc i0(); prg p0();\n"
    "  task t; event te; event ta [1:3]; event tm [0:1][3:5];\n"
    "    fork begin @te; hits |= 1; end begin @(ta[2]); late |= 1; end\n"
    "      begin @(tm[1][4]); late |= 2; end join_none #2;\n"
    "  endtask\n"
    "  function int f; event fe; return fe.triggered; endfunction\n"
    "  if (1) begin : g event ge; event ga [1:3]; event gm [0:1][3:5];\n"
    "    initial begin @ge; hits |= 2; end\n"
    "    initial begin @(ga[2]); hits |= 4; end\n"
    "    initial begin @(gm[1][4]); hits |= 8; end\n"
    "  end\n"
    "  initial begin : nb event be; event ba [1:3]; event bm [0:1][3:5];\n"
    "    fork begin @be; hits |= 16; end begin @(ba[2]); late |= 4; end\n"
    "      begin @(bm[1][4]); late |= 8; end join\n"
    "  end\n"
    "  initial fork : nf event ke; event ka [1:3]; event km [0:1][3:5];\n"
    "    begin @ke; hits |= 32; end begin @(ka[2]); late |= 16; end\n"
    "    begin @(km[1][4]); late |= 32; end\n"
    "  join\n"
    "  initial begin @me; hits |= 64; end\n"
    "  initial begin @(ma[2]); hits |= 128; end\n"
    "  initial begin @(mm[1][4]); hits |= 256; end\n"
    "  initial begin @(pkg::pe); hits |= 512; end\n"
    "  initial begin @(pkg::pa[2]); late |= 64; end\n"
    "  initial begin @(pkg::pm[1][4]); late |= 128; end\n"
    "  initial begin @ue; hits |= 1024; end\n"
    "  initial begin @(ua[2]); late |= 256; end\n"
    "  initial begin @(um[1][4]); late |= 512; end\n"
    "  initial t();\n"
    "  initial begin #1 $put; fired = f(); end\n"
    "endmodule\n";

constexpr Place kInstancesPackageUnitGenerateAndNamedBlocks[] = {
    kModule, kInterface, kProgram, kPackage, kUnit, kGenerate, kBlock, kFork};
constexpr Place kSubroutineAndBlocks[] = {kTask, kBlock, kFork};

TEST_F(EventPutsOfEveryPlace,
       APutTriggersAnInstancePackageUnitGenerateOrNamedBlocksEvent) {
  Putter() = [] {
    for (const Place& p : kInstancesPackageUnitGenerateAndNamedBlocks) {
      vpi_put_value(EventIn(p), nullptr, nullptr, vpiNoDelay);
    }
  };
  Run(kWaitersOfEveryPlace);
  EXPECT_EQ(IntegerOf(By("top.hits")), 2 | 16 | 32 | 64 | 512 | 1024);
  EXPECT_EQ(IntegerOf(By("top.i0.hits")), 1);
  EXPECT_EQ(IntegerOf(By("top.p0.hits")), 1);
}

TEST_F(EventPutsOfEveryPlace, DISABLED_APutTriggersATasksEvent) {
  Putter() = [] {
    vpi_put_value(EventIn(kTask), nullptr, nullptr, vpiNoDelay);
  };
  Run(kWaitersOfEveryPlace);
  EXPECT_EQ(IntegerOf(By("top.hits")), 1);
}

TEST_F(EventPutsOfEveryPlace, DISABLED_APutTriggersAFunctionsEvent) {
  Putter() = [] {
    vpi_put_value(EventIn(kFunction), nullptr, nullptr, vpiNoDelay);
  };
  Run(kWaitersOfEveryPlace);
  EXPECT_EQ(IntegerOf(By("top.fired")), 1);
}

TEST_F(EventPutsOfEveryPlace,
       APutTriggersAnInstanceOrGenerateBlocksArrayElement) {
  Putter() = [] {
    for (const Place& p : kInstancesAndGenerateBlock) {
      vpi_put_value(ElementIn(p), nullptr, nullptr, vpiNoDelay);
      vpi_put_value(CellIn(p, 1, 4), nullptr, nullptr, vpiNoDelay);
    }
  };
  Run(kWaitersOfEveryPlace);
  EXPECT_EQ(IntegerOf(By("top.hits")), 4 | 8 | 128 | 256);
  EXPECT_EQ(IntegerOf(By("top.i0.hits")), 2 | 4);
  EXPECT_EQ(IntegerOf(By("top.p0.hits")), 2 | 4);
}

TEST_F(EventPutsOfEveryPlace,
       DISABLED_APutTriggersASubroutineOrBlocksArrayElement) {
  Putter() = [] {
    for (const Place& p : kSubroutineAndBlocks) {
      vpi_put_value(ElementIn(p), nullptr, nullptr, vpiNoDelay);
      vpi_put_value(CellIn(p, 1, 4), nullptr, nullptr, vpiNoDelay);
    }
  };
  Run(kWaitersOfEveryPlace);
  EXPECT_EQ(IntegerOf(By("top.late")), 63);
}

TEST_F(EventPutsOfEveryPlace,
       DISABLED_APutTriggersAPackageOrTheUnitsArrayElement) {
  Putter() = [] {
    for (const Place& p : {kPackage, kUnit}) {
      vpi_put_value(ElementIn(p), nullptr, nullptr, vpiNoDelay);
      vpi_put_value(CellIn(p, 1, 4), nullptr, nullptr, vpiNoDelay);
    }
  };
  Run(kWaitersOfEveryPlace);
  EXPECT_EQ(IntegerOf(By("top.late")), 64 | 128 | 256 | 512);
}

constexpr Place kInstancesPackageUnitAndGenerateBlock[] = {
    kModule, kInterface, kProgram, kPackage, kUnit, kGenerate};
constexpr Place kPackageTaskBlocksAndUnit[] = {kPackage, kTask, kBlock, kFork,
                                               kUnit};

TEST_F(EventPutsOfEveryPlace,
       AnInstancePackageUnitOrGenerateBlocksEventReachesItsWaiter) {
  Putter() = [] {};
  Run(kWaitersOfEveryPlace);
  ForEach(kInstancesPackageUnitAndGenerateBlock,
          [](const Place& p) { ExpectOneWaiter(EventIn(p)); });
}

TEST_F(EventPutsOfEveryPlace,
       DISABLED_ATaskOrNamedBlocksEventReachesItsWaiter) {
  Putter() = [] {};
  Run(kWaitersOfEveryPlace);
  ForEach(kSubroutineAndBlocks,
          [](const Place& p) { ExpectOneWaiter(EventIn(p)); });
}

TEST_F(EventPutsOfEveryPlace,
       AnInstanceOrGenerateBlocksArrayElementReachesItsWaiter) {
  Putter() = [] {};
  Run(kWaitersOfEveryPlace);
  ForEach(kInstancesAndGenerateBlock, [](const Place& p) {
    ExpectOneWaiter(ElementIn(p));
    ExpectOneWaiter(CellIn(p, 1, 4));
  });
}

TEST_F(EventPutsOfEveryPlace,
       DISABLED_APackageTaskBlockOrTheUnitsArrayElementReachesItsWaiter) {
  Putter() = [] {};
  Run(kWaitersOfEveryPlace);
  ForEach(kPackageTaskBlocksAndUnit, [](const Place& p) {
    ExpectOneWaiter(ElementIn(p));
    ExpectOneWaiter(CellIn(p, 1, 4));
  });
}

}  // namespace
}  // namespace delta
