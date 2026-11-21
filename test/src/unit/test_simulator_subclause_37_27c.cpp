#include <gtest/gtest.h>

#include "fixture_vpi_named_events.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

constexpr Place kClassObject = {"top.c", "top", "", 'c'};
constexpr Place kClassStatics = {"C", "top", "top.C::", 's'};
constexpr Place kClassPlaces[] = {kClassObject, kClassStatics};

constexpr const char* kClassEvents =
    "module top;\n"
    "  class C; event ce; event ca [1:3]; event cm [0:1][3:5];\n"
    "    static event se; static event sa [1:3]; static event sm [0:1][3:5];\n"
    "  endclass\n"
    "  C c = new;\n"
    "endmodule\n";

TEST_F(EventsOfEveryPlace, AClassesEventsReachTheirTypespecs) {
  Run(kClassEvents);
  vpiHandle defn = Named(vpiClassDefn, By("top"), "C");
  ASSERT_NE(defn, nullptr);
  for (const char* name : {"ce", "se"}) {
    EXPECT_EQ(KindReached(vpiTypespec, Named(vpiNamedEvent, defn, name)),
              vpiEventTypespec)
        << name;
  }
  for (const char* name : {"ca", "sa"}) {
    vpiHandle array = Named(vpiNamedEventArray, defn, name);
    vpiHandle typespec =
        array == nullptr ? nullptr : vpi_handle(vpiTypespec, array);
    EXPECT_EQ(KindOf(typespec), vpiArrayTypespec) << name;
    EXPECT_EQ(KindReached(vpiElemTypespec, typespec), vpiEventTypespec) << name;
  }
}

TEST_F(EventsOfEveryPlace, AClassesEventsAreNamedAndOnlyStaticOnesFullyNamed) {
  Run(kClassEvents);
  vpiHandle defn = Named(vpiClassDefn, By("top"), "C");
  ASSERT_NE(defn, nullptr);
  vpiHandle se = Named(vpiNamedEvent, defn, "se");
  vpiHandle sa = Named(vpiNamedEventArray, defn, "sa");
  EXPECT_EQ(Str(vpiName, Named(vpiNamedEvent, defn, "ce")), "ce");
  EXPECT_EQ(Str(vpiName, Named(vpiNamedEventArray, defn, "ca")), "ca");
  EXPECT_EQ(Str(vpiName, se), "se");
  EXPECT_EQ(Str(vpiName, sa), "sa");
  EXPECT_EQ(Str(vpiFullName, se), "top.C::se");
  EXPECT_EQ(Str(vpiFullName, sa), "top.C::sa");
  vpiHandle sm = Named(vpiNamedEventArray, defn, "sm");
  EXPECT_EQ(Str(vpiName, sm), "sm");
  EXPECT_EQ(Str(vpiFullName, sm), "top.C::sm");
}

TEST_F(EventsOfEveryPlace, DISABLED_AClassesNonStaticEventHasNoFullName) {
  Run(kClassEvents);
  vpiHandle defn = Named(vpiClassDefn, By("top"), "C");
  ASSERT_NE(defn, nullptr);
  EXPECT_EQ(Str(vpiFullName, Named(vpiNamedEvent, defn, "ce")), "<null>");
}

TEST_F(EventsOfEveryPlace, DISABLED_AClassesNonStaticEventArrayHasNoFullName) {
  Run(kClassEvents);
  vpiHandle defn = Named(vpiClassDefn, By("top"), "C");
  ASSERT_NE(defn, nullptr);
  EXPECT_EQ(Str(vpiFullName, Named(vpiNamedEventArray, defn, "ca")), "<null>");
}

TEST_F(EventsOfEveryPlace, AClassesEventsAndEventArraysHaveTheirKinds) {
  Run(kClassEvents);
  ForEach(kClassPlaces, ExpectKinds);
}

TEST_F(EventsOfEveryPlace, AClassesStaticEventArrayIsOfEvents) {
  Run(kClassEvents);
  ExpectArraysOfEvents(kClassStatics);
}

TEST_F(EventsOfEveryPlace, DISABLED_AClassObjectsEventHasTheEventTypespec) {
  Run(kClassEvents);
  ExpectEventTypespec(kClassObject);
}

TEST_F(EventsOfEveryPlace, DISABLED_AClassObjectsEventArrayIsOfEvents) {
  Run(kClassEvents);
  ExpectArraysOfEvents(kClassObject);
}

TEST_F(EventsOfEveryPlace, DISABLED_AClassesArrayElementIsAnEvent) {
  Run(kClassEvents);
  ForEach(kClassPlaces, ExpectElementKinds);
}

TEST_F(EventsOfEveryPlace, DISABLED_AClassesArrayElementHasTheEventTypespec) {
  Run(kClassEvents);
  ForEach(kClassPlaces, ExpectElementTypespecs);
}

TEST_F(EventsOfEveryPlace,
       DISABLED_AClassesStaticArrayElementsNameCarriesItsIndices) {
  Run(kClassEvents);
  ExpectElementNames(kClassStatics);
}

TEST_F(EventsOfEveryPlace, DISABLED_AClassObjectsEventIsNamedButNotFullyNamed) {
  Run(kClassEvents);
  EXPECT_EQ(Str(vpiName, EventIn(kClassObject)), "ce");
  EXPECT_EQ(Str(vpiFullName, EventIn(kClassObject)), "<null>");
}

TEST_F(EventsOfEveryPlace,
       DISABLED_AClassObjectsEventArrayIsNamedButNotFullyNamed) {
  Run(kClassEvents);
  EXPECT_EQ(Str(vpiName, ArrayIn(kClassObject)), "ca");
  EXPECT_EQ(Str(vpiFullName, ArrayIn(kClassObject)), "<null>");
  EXPECT_EQ(Str(vpiName, GridIn(kClassObject)), "cm");
  EXPECT_EQ(Str(vpiFullName, GridIn(kClassObject)), "<null>");
}

TEST_F(EventsOfEveryPlace,
       DISABLED_AClassObjectsArrayElementIsNamedButNotFullyNamed) {
  Run(kClassEvents);
  EXPECT_EQ(Str(vpiName, ElementIn(kClassObject)), "ca[2]");
  EXPECT_EQ(Str(vpiFullName, ElementIn(kClassObject)), "<null>");
  EXPECT_EQ(Str(vpiName, CellIn(kClassObject, 1, 4)), "cm[1][4]");
  EXPECT_EQ(Str(vpiFullName, CellIn(kClassObject, 1, 4)), "<null>");
}

TEST_F(EventsOfEveryPlace, DISABLED_AClassesEventArrayIteratesEveryElement) {
  Run(kClassEvents);
  ForEach(kClassPlaces, ExpectRowIterated);
  ForEach(kClassPlaces, ExpectGridIterated);
}

TEST_F(EventsOfEveryPlace, DISABLED_AClassesArrayElementIsAnArrayMember) {
  Run(kClassEvents);
  ForEach(kClassPlaces, ExpectElementsAreArrayMembers);
}

TEST_F(EventsOfEveryPlace, AClassesScalarEventIsNoArrayMemberAndHasNoIndex) {
  Run(kClassEvents);
  ForEach(kClassPlaces, [](const Place& p) {
    vpiHandle event = EventIn(p);
    ASSERT_NE(event, nullptr);
    EXPECT_EQ(Flag(vpiArrayMember, event), 0);
    EXPECT_EQ(Flag(vpiArray, event), 0);
    EXPECT_EQ(vpi_iterate(vpiIndex, event), nullptr);
  });
}

TEST_F(EventsOfEveryPlace,
       DISABLED_AClassesArrayElementIsAnArrayMemberByTheDeprecatedProperty) {
  Run(kClassEvents);
  ForEach(kClassPlaces, ExpectElementsFlaggedAsArrays);
}

TEST_F(EventsOfEveryPlace, DISABLED_AClassesArrayElementsIndicesRunOutward) {
  Run(kClassEvents);
  ForEach(kClassPlaces, ExpectElementIndices);
}

TEST_F(EventsOfEveryPlace, DISABLED_AClassesEventArrayRangesRunLeftToRight) {
  Run(kClassEvents);
  ForEach(kClassPlaces, ExpectRanges);
}

TEST_F(EventsOfEveryPlace, DISABLED_AClassesEventArrayIsIndexedByItsIndices) {
  Run(kClassEvents);
  ForEach(kClassPlaces, ExpectIndexedAccess);
}

TEST_F(EventsOfEveryPlace,
       DISABLED_AClassesTwoDimensionalArraysElementHasTheArrayAsParent) {
  Run(kClassEvents);
  ForEach(kClassPlaces, ExpectCellParent);
}

TEST_F(EventsOfEveryPlace, AClassObjectsEventAndEventArrayAreDynamic) {
  Run(kClassEvents);
  const Place& p = kClassObject;
  for (vpiHandle event : {EventIn(p), ArrayIn(p), GridIn(p)}) {
    ExpectLifetime(event, 1, vpiDynamicScheme);
  }
}

TEST_F(EventsOfEveryPlace, DISABLED_AClassObjectsArrayElementIsDynamic) {
  Run(kClassEvents);
  const Place& p = kClassObject;
  for (vpiHandle event : {ElementIn(p), CellIn(p, 1, 4)}) {
    ExpectLifetime(event, 1, vpiDynamicScheme);
  }
}

TEST_F(EventsOfEveryPlace, AClassesStaticEventAndEventArrayAreStatic) {
  Run(kClassEvents);
  ExpectStaticDeclarations(kClassStatics);
}

TEST_F(EventsOfEveryPlace, DISABLED_AClassesStaticArrayElementIsStatic) {
  Run(kClassEvents);
  ExpectStaticElements(kClassStatics);
}

TEST_F(EventsOfEveryPlace,
       AClassesStaticEventAndEventArrayReachTheirInstanceAndModule) {
  Run(kClassEvents);
  const Place& p = kClassStatics;
  for (vpiHandle event : {EventIn(p), ArrayIn(p), GridIn(p)}) {
    ASSERT_NE(event, nullptr);
    EXPECT_EQ(Reached(vpiInstance, event), VpiObjectOf(By("top")));
    EXPECT_EQ(Reached(vpiModule, event), VpiObjectOf(By("top")));
  }
}

TEST_F(EventsOfEveryPlace,
       DISABLED_AClassesStaticArrayElementReachesItsInstanceAndModule) {
  Run(kClassEvents);
  ExpectElementInstanceAndModule(kClassStatics);
}

TEST_F(EventsOfEveryPlace, DISABLED_AClassesEventReachesItsScope) {
  Run(kClassEvents);
  ForEach(kClassPlaces, [](const Place& p) {
    vpiHandle event = EventIn(p);
    ASSERT_NE(event, nullptr);
    EXPECT_EQ(Reached(vpiScope, event), VpiObjectOf(ScopeOf(p)));
  });
}

TEST_F(EventsOfEveryPlace, DISABLED_AClassesArrayElementReachesItsScope) {
  Run(kClassEvents);
  ForEach(kClassPlaces, [](const Place& p) {
    EXPECT_EQ(Reached(vpiScope, ElementIn(p)), VpiObjectOf(ScopeOf(p)));
    EXPECT_EQ(Reached(vpiScope, CellIn(p, 1, 4)), VpiObjectOf(ScopeOf(p)));
  });
}

constexpr const char* kClassWaiters =
    "module top; int hits;\n"
    "  class C; event ce; event ca [1:3]; event cm [0:1][3:5];\n"
    "    static event se; static event sa [1:3]; static event sm [0:1][3:5];\n"
    "  endclass\n"
    "  C c = new;\n"
    "  initial begin @(c.ce); hits |= 1; end\n"
    "  initial begin @(c.ca[2]); hits |= 2; end\n"
    "  initial begin @(c.cm[1][4]); hits |= 4; end\n"
    "  initial begin @(C::se); hits |= 8; end\n"
    "  initial begin @(C::sa[2]); hits |= 16; end\n"
    "  initial begin @(C::sm[1][4]); hits |= 32; end\n"
    "  initial #1 $put;\n"
    "endmodule\n";

TEST_F(EventPutsOfEveryPlace, DISABLED_AClassesEventReachesItsWaiter) {
  Putter() = [] {};
  Run(kClassWaiters);
  ForEach(kClassPlaces, [](const Place& p) { ExpectOneWaiter(EventIn(p)); });
}

TEST_F(EventPutsOfEveryPlace, DISABLED_AClassesArrayElementReachesItsWaiter) {
  Putter() = [] {};
  Run(kClassWaiters);
  ForEach(kClassPlaces, [](const Place& p) {
    ExpectOneWaiter(ElementIn(p));
    ExpectOneWaiter(CellIn(p, 1, 4));
  });
}

TEST_F(EventPutsOfEveryPlace, DISABLED_APutTriggersAClassesEvent) {
  Putter() = [] {
    for (const Place& p : kClassPlaces) {
      vpi_put_value(EventIn(p), nullptr, nullptr, vpiNoDelay);
    }
  };
  Run(kClassWaiters);
  EXPECT_EQ(IntegerOf(By("top.hits")), 1 | 8);
}

TEST_F(EventPutsOfEveryPlace, DISABLED_APutTriggersAClassesArrayElement) {
  Putter() = [] {
    for (const Place& p : kClassPlaces) {
      vpi_put_value(ElementIn(p), nullptr, nullptr, vpiNoDelay);
      vpi_put_value(CellIn(p, 1, 4), nullptr, nullptr, vpiNoDelay);
    }
  };
  Run(kClassWaiters);
  EXPECT_EQ(IntegerOf(By("top.hits")), 2 | 4 | 16 | 32);
}

}  // namespace
}  // namespace delta
