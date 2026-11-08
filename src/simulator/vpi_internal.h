#pragma once

#include <cstdint>
#include <string_view>
#include <unordered_set>
#include <vector>

#include "common/types.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

class Scheduler;

inline PLI_BYTE8* VpiText(const char* text) {
  return const_cast<PLI_BYTE8*>(text);
}

VpiObject* VpiResolveSameObject(VpiObject* obj);

bool VpiIsScopeBodyStmtType(int type);

bool VpiIsAtomicStmtObject(VpiHandle obj);
bool VpiIsScopeBodyStmtObject(VpiHandle obj);

bool VpiIsInternalScopeType(int type);
bool VpiIsScopeObject(VpiHandle obj);

bool VpiCollectNestedObjects(int type, VpiHandle ref, VpiHandle iter);

VpiHandle VpiNestedScopeNamed(VpiHandle parent, std::string_view name);

bool TryResolveStmtScopeRelation(int type, VpiHandle ref, VpiHandle& out);
bool TryResolveVariableScopeRelation(int type, VpiHandle ref, VpiHandle& out);

bool VpiIsBodyStmtOwnerType(int type);

VpiHandle VpiExpectElseStmt(VpiHandle expect);

VpiHandle VpiForHeaderStmt(int type, VpiHandle for_stmt);

void VpiCollectForHeaderStmts(int type, VpiHandle for_stmt, VpiHandle iter);

void VpiCollectTfCallArguments(VpiHandle call, VpiHandle iter);

bool TryResolveProcessAndStmtRelation(int type, VpiHandle ref, VpiHandle& out);

bool TryResolveSpecifyRelation(int type, VpiHandle ref, VpiHandle& out);

bool VpiIsCallbackHostType(int type);

void VpiCollectCallbackObjects(VpiHandle ref,
                               const std::vector<VpiHandle>& cb_handles,
                               const std::vector<s_cb_data>& callbacks,
                               VpiHandle iter);

bool VpiIsVirtualInterfaceArray(VpiHandle obj);

void VpiCollectInstanceAssertions(VpiHandle scope, VpiHandle iter);

bool VpiObjectIsPrimitive(int type);

const char* VpiCompatibilityUnsupportedConstruct(
    int mode, const std::vector<VpiObject*>& objects);

VpiHandle VpiIterateInCompatibilityMode(int type, VpiHandle ref, int mode);

int VpiGetInCompatibilityMode(int property, VpiHandle obj, int mode);

bool VpiPutValueBits(const s_vpi_value& value, uint32_t width,
                     std::vector<Logic4Word>& words);

uint32_t VpiPutWidth(const VpiObject& obj);

void VpiWriteDecodedBits(VpiObject& obj, const std::vector<Logic4Word>& bits,
                         uint32_t width);

void VpiSchedulePut(VpiObject& obj, const s_vpi_value& value, int mode,
                    Scheduler& scheduler, VpiObject& event);

uint64_t VpiPutDelayTicks(const VpiObject& obj, const s_vpi_time& time,
                          int sim_unit);

int VpiObjectTimeUnit(const VpiObject& obj, int sim_unit);

std::vector<std::string_view> VpiNamePathComponents(
    std::string_view name,
    const std::unordered_set<std::string_view>& whole_names);

std::vector<std::string_view> VpiHandleNameComponents(std::string_view name);

bool HasCallbackFor(const std::vector<s_cb_data>& callbacks, int reason);

}  // namespace delta
