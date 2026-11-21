#pragma once

#include <gtest/gtest.h>

#include <cstddef>
#include <functional>
#include <span>
#include <string>
#include <string_view>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

struct Place {
  const char* scope;
  const char* instance;
  const char* prefix;
  char letter;
};

inline constexpr Place kModule = {"top", "top", "top.", 'm'};
inline constexpr Place kInterface = {"top.i0", "top.i0", "top.i0.", 'i'};
inline constexpr Place kProgram = {"top.p0", "top.p0", "top.p0.", 'q'};
inline constexpr Place kPackage = {"pkg", "pkg", "pkg::", 'p'};
inline constexpr Place kTask = {"t", "top", "top.t.", 't'};
inline constexpr Place kFunction = {"f", "top", "top.f.", 'f'};
inline constexpr Place kGenerate = {"top.g", "top", "top.g.", 'g'};
inline constexpr Place kBlock = {"top.nb", "top", "top.nb.", 'b'};
inline constexpr Place kFork = {"top.nf", "top", "top.nf.", 'k'};
inline constexpr Place kUnit = {"$unit", "$unit", "$unit::", 'u'};

inline constexpr Place kEveryPlace[] = {
    kModule,   kInterface, kProgram, kPackage, kTask,
    kFunction, kGenerate,  kBlock,   kFork,    kUnit};

inline vpiHandle UnitPackage() {
  vpiHandle it = vpi_iterate(vpiPackage, nullptr);
  if (it == nullptr) return nullptr;
  while (vpiHandle pkg = vpi_scan(it)) {
    if (vpi_get(vpiUnit, pkg) == 1) return pkg;
  }
  return nullptr;
}

class EventsOfEveryPlace : public VpiDesignRun {
 protected:
  static std::string NameIn(const Place& p, char kind) {
    return std::string{p.letter, kind};
  }

  static vpiHandle ScopeOf(const Place& p) {
    const std::string_view kScope(p.scope);
    if (kScope == "$unit") return UnitPackage();
    if (kScope == "C") return Named(vpiClassDefn, By("top"), kScope);
    if (kScope == "top.c") return Through(vpiClassObj, By("top.c"));
    if (kScope == "t" || kScope == "f") {
      return Named(vpiTaskFunc, By("top"), kScope);
    }
    return By(p.scope);
  }

  static vpiHandle InstanceOf(const Place& p) {
    const std::string_view kInstance(p.instance);
    return kInstance == "$unit" ? UnitPackage() : By(p.instance);
  }

  static vpiHandle ModuleOf(const Place& p) {
    const std::string_view kInstance(p.instance);
    return kInstance == "pkg" || kInstance == "$unit" ? nullptr : By("top");
  }

  static vpiHandle EventIn(const Place& p) {
    return Named(vpiNamedEvent, ScopeOf(p), NameIn(p, 'e'));
  }

  static vpiHandle ArrayIn(const Place& p) {
    return Named(vpiNamedEventArray, ScopeOf(p), NameIn(p, 'a'));
  }

  static vpiHandle GridIn(const Place& p) {
    return Named(vpiNamedEventArray, ScopeOf(p), NameIn(p, 'm'));
  }

  static vpiHandle ElementIn(const Place& p) {
    vpiHandle array = ArrayIn(p);
    return array == nullptr ? nullptr : vpi_handle_by_index(array, 2);
  }

  static vpiHandle CellIn(const Place& p, PLI_INT32 row, PLI_INT32 column) {
    vpiHandle grid = GridIn(p);
    PLI_INT32 index[] = {row, column};
    return grid == nullptr ? nullptr
                           : vpi_handle_by_multi_index(grid, 2, index);
  }

  static int KindOf(vpiHandle obj) {
    return obj == nullptr ? 0 : vpi_get(vpiType, obj);
  }

  static vpiHandle Through(int relation, vpiHandle ref) {
    return ref == nullptr ? nullptr : vpi_handle(relation, ref);
  }

  static int KindReached(int relation, vpiHandle ref) {
    return KindOf(Through(relation, ref));
  }

  static VpiObject* Reached(int relation, vpiHandle ref) {
    return ref == nullptr ? nullptr : VpiObjectOf(vpi_handle(relation, ref));
  }

  static std::string Str(int property, vpiHandle obj) {
    const char* text = obj == nullptr ? nullptr : vpi_get_str(property, obj);
    return text == nullptr ? "<null>" : text;
  }

  static int Flag(int property, vpiHandle obj) {
    return obj == nullptr ? -1 : vpi_get(property, obj);
  }

  static void ForEach(std::span<const Place> places,
                      const std::function<void(const Place&)>& check) {
    for (const Place& p : places) {
      SCOPED_TRACE(p.scope);
      check(p);
    }
  }

  static void ExpectKinds(const Place& p) {
    EXPECT_EQ(KindOf(EventIn(p)), vpiNamedEvent);
    EXPECT_EQ(KindOf(ArrayIn(p)), vpiNamedEventArray);
    EXPECT_EQ(KindOf(GridIn(p)), vpiNamedEventArray);
  }

  static void ExpectElementTypespecs(const Place& p) {
    EXPECT_EQ(KindReached(vpiTypespec, ElementIn(p)), vpiEventTypespec);
    EXPECT_EQ(KindReached(vpiTypespec, CellIn(p, 1, 4)), vpiEventTypespec);
  }

  static void ExpectGridIterated(const Place& p) {
    ExpectElementsIterated(GridIn(p), 6U);
  }

  static void ExpectElementsFlaggedAsArrays(const Place& p) {
    EXPECT_EQ(Flag(vpiArray, ElementIn(p)), 1);
    EXPECT_EQ(Flag(vpiArray, CellIn(p, 1, 4)), 1);
  }

  static void ExpectCellParent(const Place& p) {
    EXPECT_EQ(Reached(vpiParent, CellIn(p, 1, 4)), VpiObjectOf(GridIn(p)));
  }

  static void ExpectLifetime(vpiHandle event, int automatic, int scheme) {
    EXPECT_EQ(Flag(vpiAutomatic, event), automatic);
    EXPECT_EQ(Flag(vpiAllocScheme, event), scheme);
  }

  static void ExpectStaticDeclarations(const Place& p) {
    for (vpiHandle event : {EventIn(p), ArrayIn(p), GridIn(p)}) {
      ExpectLifetime(event, 0, vpiOtherScheme);
    }
  }

  static void ExpectStaticElements(const Place& p) {
    ExpectLifetime(ElementIn(p), 0, vpiOtherScheme);
    ExpectLifetime(CellIn(p, 1, 4), 0, vpiOtherScheme);
  }

  static void ExpectOneWaiter(vpiHandle event) {
    ASSERT_NE(event, nullptr);
    const std::vector<vpiHandle> kWaiters =
        ObjectsOf(vpiWaitingProcesses, event);
    ASSERT_EQ(kWaiters.size(), 1U);
    EXPECT_EQ(KindOf(kWaiters[0]), vpiThread);
  }

  static void ExpectElementKinds(const Place& p) {
    EXPECT_EQ(KindOf(ElementIn(p)), vpiNamedEvent);
    EXPECT_EQ(KindOf(CellIn(p, 1, 4)), vpiNamedEvent);
  }

  static void ExpectEventTypespec(const Place& p) {
    EXPECT_EQ(KindReached(vpiTypespec, EventIn(p)), vpiEventTypespec);
  }

  static void ExpectArraysOfEvents(const Place& p) {
    vpiHandle row = Through(vpiTypespec, ArrayIn(p));
    EXPECT_EQ(KindOf(row), vpiArrayTypespec);
    EXPECT_EQ(KindReached(vpiElemTypespec, row), vpiEventTypespec);
    vpiHandle grid = Through(vpiTypespec, GridIn(p));
    EXPECT_EQ(KindOf(grid), vpiArrayTypespec);
    vpiHandle inner = Through(vpiElemTypespec, grid);
    EXPECT_EQ(KindOf(inner), vpiArrayTypespec);
    EXPECT_EQ(KindReached(vpiElemTypespec, inner), vpiEventTypespec);
  }

  static void ExpectElementNames(const Place& p) {
    const std::string kElement = NameIn(p, 'a') + "[2]";
    const std::string kCell = NameIn(p, 'm') + "[1][4]";
    EXPECT_EQ(Str(vpiName, ElementIn(p)), kElement);
    EXPECT_EQ(Str(vpiFullName, ElementIn(p)), p.prefix + kElement);
    EXPECT_EQ(Str(vpiName, CellIn(p, 1, 4)), kCell);
    EXPECT_EQ(Str(vpiFullName, CellIn(p, 1, 4)), p.prefix + kCell);
  }

  static void ExpectElementInstanceAndModule(const Place& p) {
    vpiHandle element = ElementIn(p);
    ASSERT_NE(element, nullptr);
    EXPECT_EQ(Reached(vpiInstance, element), VpiObjectOf(InstanceOf(p)));
    EXPECT_EQ(Reached(vpiModule, element), VpiObjectOf(ModuleOf(p)));
  }

  static void ExpectElementsIterated(vpiHandle array, std::size_t count) {
    ASSERT_NE(array, nullptr);
    const std::vector<vpiHandle> kElements = ObjectsOf(vpiNamedEvent, array);
    EXPECT_EQ(kElements.size(), count);
    for (vpiHandle element : kElements) {
      EXPECT_EQ(KindOf(element), vpiNamedEvent);
      EXPECT_EQ(Reached(vpiParent, element), VpiObjectOf(array));
    }
  }

  static void ExpectRowIterated(const Place& p) {
    ExpectElementsIterated(ArrayIn(p), 3U);
  }

  static void ExpectElementsAreArrayMembers(const Place& p) {
    EXPECT_EQ(Flag(vpiArrayMember, ElementIn(p)), 1);
    EXPECT_EQ(Flag(vpiArrayMember, CellIn(p, 1, 4)), 1);
  }

  static void ExpectElementIndices(const Place& p) {
    EXPECT_EQ(IntsOf(vpiIndex, ElementIn(p)), std::vector<int>{2});
    EXPECT_EQ(IntsOf(vpiIndex, CellIn(p, 1, 4)), (std::vector<int>{4, 1}));
  }

  static void ExpectRanges(const Place& p) {
    EXPECT_EQ(BoundsOf(ArrayIn(p)), (std::vector<int>{1, 3}));
    EXPECT_EQ(BoundsOf(GridIn(p)), (std::vector<int>{0, 1, 3, 5}));
  }

  static void ExpectIndexedAccess(const Place& p) {
    EXPECT_EQ(Reached(vpiParent, ElementIn(p)), VpiObjectOf(ArrayIn(p)));
    ASSERT_NE(CellIn(p, 1, 4), nullptr);
    EXPECT_NE(VpiObjectOf(CellIn(p, 1, 4)), VpiObjectOf(CellIn(p, 0, 4)));
    EXPECT_NE(VpiObjectOf(CellIn(p, 1, 4)), VpiObjectOf(CellIn(p, 1, 3)));
    EXPECT_EQ(CellIn(p, 1, 2), nullptr);
    EXPECT_EQ(vpi_handle_by_index(ArrayIn(p), 0), nullptr);
  }
};

inline std::function<void()>& Putter() {
  static std::function<void()> putter;
  return putter;
}

class EventPutsOfEveryPlace : public EventsOfEveryPlace {
 protected:
  void SetUp() override {
    EventsOfEveryPlace::SetUp();
    s_vpi_systf_data data = {};
    data.type = vpiSysTask;
    data.tfname = VpiText("$put");
    data.calltf = [](PLI_BYTE8*) -> PLI_INT32 {
      Putter()();
      return 0;
    };
    ASSERT_NE(vpi_register_systf(&data), nullptr);
  }
};

}  // namespace delta
