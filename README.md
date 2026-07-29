script_name("SF Integration")
script_version("2.1")
script_version_number(21)
script_author("FYP & Modified")
script_description("Integrate MoonLoader with SAMPFUNCS")
script_properties('work-in-pause')

require "lib.sampfuncs"
require "lib.moonloader"
local vkeys = require 'lib.vkeys'
local ffi = require "ffi"
local vector = require "vector3d"
local sampev = require('samp.events')
local imgui = require('mimgui')
local encoding = require('encoding')

encoding.default = 'CP1251'

--------------------------------------------------------------------------------
-- CSTRUCTS & FFI
--------------------------------------------------------------------------------
local getbonePosition = ffi.cast("int (__thiscall*)(void*, float*, int, bool)", 0x5E4280)

--------------------------------------------------------------------------------
-- AIMBOT VARS
--------------------------------------------------------------------------------
local stun_anims = {
    'DAM_armL_frmBK', 'DAM_armL_frmFT', 'DAM_armL_frmLT', 'DAM_armR_frmBK', 'DAM_armR_frmFT', 'DAM_armR_frmRT',
    'DAM_LegL_frmBK', 'DAM_LegL_frmFT', 'DAM_LegL_frmLT', 'DAM_LegR_frmBK', 'DAM_LegR_frmFT', 'DAM_LegR_frmRT',
    'DAM_stomach_frmBK', 'DAM_stomach_frmFT', 'DAM_stomach_frmLT', 'DAM_stomach_frmRT'
}

local mainWindow = imgui.new.bool(false)
local smooth = imgui.new.float(5.0)
local radius = imgui.new.float(0.6)
local enable = imgui.new.bool(false)
local clistFilter = imgui.new.bool(false)
local visibleCheck = imgui.new.bool(false)
local checkStuned = imgui.new.bool(false)
local checkPause = imgui.new.bool(false)
local idFilter = imgui.new.bool(false)
local excludeIDsBuffer = imgui.new.char[256]("-1")
local heightOffset = imgui.new.float(0.0)
local useHeightOffset = imgui.new.bool(true)
local fovAdjust = imgui.new.float(70.0)
local disableOnZoom = imgui.new.bool(false)
local zOffset = imgui.new.float(0.0)
local useZOffset = imgui.new.bool(true)

--------------------------------------------------------------------------------
-- INTEGRATION VARS
--------------------------------------------------------------------------------
local function isMonser01()
    if not isSampAvailable() then return false end
    local ip, port = sampGetCurrentServerAddress()
    local name = sampGetCurrentServerName()
    return ip == "185.71.66.13" or (name:lower():find("monser") and (name:find("01") or name:find("1")))
end

local lastReportSender = -1
local lastReportTarget = -1
local activeReportSender = -1
local activeReportTarget = -1

local showOwnKeys = false
local warningsEnabled = false

local lastWarnTime = {}
local playerChatHistory = {}

TAG = {
    TYPE_INFO      = 1,
    TYPE_DEBUG     = 2,
    TYPE_ERROR     = 3,
    TYPE_WARN      = 4,
    TYPE_SYSTEM    = 5,
    TYPE_FATAL     = 6,
    TYPE_EXCEPTION = 7
}

local tracersEnabled = true
local bullets = {}
local TRACER_LIFETIME = 2.0
local LINE_THICKNESS = 1.5
local CIRCLE_RADIUS = 3.0

local COLOR_HIT    = imgui.ImVec4(0.0, 1.0, 0.0, 0.8)
local COLOR_MISS   = imgui.ImVec4(1.0, 0.0, 0.0, 0.8)
local COLOR_SILENT = imgui.ImVec4(1.0, 0.5, 0.0, 0.8)

local specStats = { shots = 0, hits = 0, misses = 0, head = 0, belly = 0, shoulders = 0, legs = 0 }

local function resetSpecStats()
    specStats.shots = 0
    specStats.hits = 0
    specStats.misses = 0
    specStats.head = 0
    specStats.belly = 0
    specStats.shoulders = 0
    specStats.legs = 0
end

local AIM_LENGTH = 2.0
local AIM_TRANSITION = 0.5
local AIM_DISTANCE = 100

local aimState = true
local aimCam = {}

local keysyncTargetId = -1
local keysyncKeys = { ["onfoot"] = {}, ["vehicle"] = {} }
local sW, sH = 0, 0
local KEYCAP = {}

logDebugMessages = false
COLOR_MSG       = 0xC0C0C0
COLOR_SCRIPTMSG = 0x7DD156
COLOR_SENDER    = 0xE0E0E0

--------------------------------------------------------------------------------
-- HELPER FUNCTIONS
--------------------------------------------------------------------------------
function fix(angle)
    if angle > math.pi then angle = angle - (math.pi * 2)
    elseif angle < -math.pi then angle = angle + (math.pi * 2) end
    return angle
end

function stringToIdList(str)
    local ids = {}
    for id in str:gmatch("[^,]+") do
        local num = tonumber(id:match("%d+"))
        if num then table.insert(ids, num) end
    end
    return ids
end

function bringFloatTo(from, dest, start_time, duration)
    local timer = os.clock() - start_time
    if timer >= 0.00 and timer <= duration then
        local count = timer / (duration / 100)
        return from + (count * (dest - from) / 100)
    end
    return (timer > duration) and dest or from
end

function getBodyPartCoordinates(id, handle)
    if doesCharExist(handle) then
        local ptr = getCharPointer(handle)
        if ptr ~= 0 then
            local pos = ffi.new("float[3]")
            getbonePosition(ffi.cast("void*", ptr), pos, id, true)
            return true, vector(pos[0], pos[1], pos[2])
        end
    end
    return false
end

function GetNearestBone(handle)
    if useHeightOffset[0] then
        return 3
    else
        local maxDist = 20000    
        local nearestBone = -1
        local bone = {42, 52, 23, 33, 3, 22, 32, 8}
        for n = 1, #bone do
            local crosshairPos = {convertGameScreenCoordsToWindowScreenCoords(339.1, 179.1)}
            local res, bonePosVec = getBodyPartCoordinates(bone[n], handle)
            if res then
                local enPos = {convert3DCoordsToScreen(bonePosVec.x, bonePosVec.y, bonePosVec.z)}
                local distance = math.sqrt((math.pow((enPos[1] - crosshairPos[1]), 2) + math.pow((enPos[2] - crosshairPos[2]), 2)))
                if distance < maxDist then
                    nearestBone = bone[n]
                    maxDist = distance
                end
            end
        end
        return nearestBone
    end
end

function GetAimbotBodyPartCoords(id, handle)
    local res, vec = getBodyPartCoordinates(id, handle)
    if res then
        local totalZOffset = 0.0
        if useHeightOffset[0] then totalZOffset = totalZOffset + heightOffset[0] end
        if useZOffset[0] then totalZOffset = totalZOffset + zOffset[0] end
        
        return vec.x, vec.y, vec.z + totalZOffset
    end
    return 0, 0, 0
end

function CheckStuned()
    for k, v in pairs(stun_anims) do
        if isCharPlayingAnim(PLAYER_PED, v) then return false end
    end
    return true
end

function GetNearestPed(fov)
    local maxDistance = 35
    local nearestPED = -1
    local excludedIDs = idFilter[0] and stringToIdList(ffi.string(excludeIDsBuffer)) or {}
    
    for i = 0, sampGetMaxPlayerId(true) do
        if sampIsPlayerConnected(i) then
            local shouldExclude = false
            for _, excludedID in ipairs(excludedIDs) do
                if i == excludedID then shouldExclude = true; break end
            end
            if not (idFilter[0] and shouldExclude) then
                local find, handle = sampGetCharHandleBySampPlayerId(i)
                if find and isCharOnScreen(handle) and not isCharDead(handle) then
                    local _, currentID = sampGetPlayerIdByCharHandle(PLAYER_PED)
                    local enX, enY, enZ = GetAimbotBodyPartCoords(GetNearestBone(handle), handle)
                    local myX, myY, myZ = getActiveCameraCoordinates()
                    local vector = {myX - enX, myY - enY, myZ - enZ}
                    local heightDiff = math.abs(myZ - enZ)
                    local adjustedFov = fov * (1 + heightDiff / 10)
                    local fovFactor = fovAdjust[0] / 70.0
                    local coefficentZ = isWidescreenOnInOptions() and (0.0778 * fovFactor) or (0.103 * fovFactor)
                    
                    local angle = {
                        (math.atan2(vector[2], vector[1]) + 0.04253),
                        (math.atan2((math.sqrt((math.pow(vector[1], 2) + math.pow(vector[2], 2)))), vector[3]) - math.pi / 2 - coefficentZ)
                    }
                    local view = {fix(representIntAsFloat(readMemory(0xB6F258, 4, false))), fix(representIntAsFloat(readMemory(0xB6F248, 4, false)))}
                    local distance = math.sqrt((math.pow(fix(angle[1] - view[1]), 2) + math.pow(fix(angle[2] - view[2]), 2))) * 57.2957795131
                    
                    if distance <= adjustedFov then
                        local myPosX, myPosY, myPosZ = getCharCoordinates(PLAYER_PED)
                        local distToPlayer = math.sqrt((math.pow((enX - myPosX), 2) + math.pow((enY - myPosY), 2) + math.pow((enZ - myPosZ), 2)))
                        if distToPlayer < maxDistance then
                            nearestPED = handle
                            maxDistance = distToPlayer
                        end
                    end
                end
            end
        end
    end
    return nearestPED
end

function smooth_aimbot()
    if enable[0] and isKeyDown(vkeys.VK_RBUTTON) then
        local isAiming = getCurrentCharWeapon(PLAYER_PED) ~= 0
        local weaponId = getCurrentCharWeapon(PLAYER_PED)
        
        if disableOnZoom[0] and isAiming and (weaponId == 30 or weaponId == 31) then
            return
        end

        local handle = GetNearestPed(radius[0])
        if handle ~= -1 then
            local _, myID = sampGetPlayerIdByCharHandle(PLAYER_PED)
            local result, playerID = sampGetPlayerIdByCharHandle(handle)
            if result then
                if (checkStuned[0] and not CheckStuned()) then return end
                if (clistFilter[0] and sampGetPlayerColor(myID) == sampGetPlayerColor(playerID)) then return end
                if (checkPause[0] and sampIsPlayerPaused(playerID)) then return end

                local myX, myY, myZ = getActiveCameraCoordinates()
                local enX, enY, enZ = GetAimbotBodyPartCoords(GetNearestBone(handle), handle)

                if not visibleCheck[0] or (visibleCheck[0] and isLineOfSightClear(myX, myY, myZ, enX, enY, enZ, true, true, false, true, true)) then
                    local vector = {myX - enX, myY - enY, myZ - enZ}
                    local fovFactor = fovAdjust[0] / 70.0
                    local coefficentZ = isWidescreenOnInOptions() and (0.0778 * fovFactor) or (0.103 * fovFactor)

                    local angle = {
                        (math.atan2(vector[2], vector[1]) + 0.04253),
                        (math.atan2((math.sqrt((math.pow(vector[1], 2) + math.pow(vector[2], 2)))), vector[3]) - math.pi / 2 - coefficentZ)
                    }

                    local view = {
                        fix(representIntAsFloat(readMemory(0xB6F258, 4, false))),
                        fix(representIntAsFloat(readMemory(0xB6F248, 4, false)))
                    }

                    local difference = {
                        fix(angle[1] - view[1]),
                        fix(angle[2] - view[2])
                    }

                    local smoothFactor = smooth[0]
                    
                    if smoothFactor <= 1.0 then
                        setCameraPositionUnfixed(view[2] + difference[2], view[1] + difference[1])
                    else
                        local sm = {difference[1] / smoothFactor, difference[2] / smoothFactor}
                        setCameraPositionUnfixed(view[2] + sm[2], view[1] + sm[1])
                    end
                end
            end
        end
    end
end

--------------------------------------------------------------------------------
-- IMGUI STYLES & RENDERING
--------------------------------------------------------------------------------
local function applyCustomStyle()
    local style = imgui.GetStyle()
    style.WindowRounding = 8.0
    style.FrameRounding = 4.0
    style.ScrollbarRounding = 4.0
    style.GrabRounding = 4.0
    style.Colors[imgui.Col.Text] = imgui.ImVec4(0.90, 0.90, 0.90, 1.00)
    style.Colors[imgui.Col.WindowBg] = imgui.ImVec4(0.10, 0.10, 0.12, 0.94)
    style.Colors[imgui.Col.FrameBg] = imgui.ImVec4(0.20, 0.20, 0.22, 0.54)
    style.Colors[imgui.Col.FrameBgHovered] = imgui.ImVec4(0.30, 0.30, 0.32, 0.70)
    style.Colors[imgui.Col.FrameBgActive] = imgui.ImVec4(0.40, 0.40, 0.42, 0.80)
    style.Colors[imgui.Col.TitleBg] = imgui.ImVec4(0.15, 0.15, 0.17, 1.00)
    style.Colors[imgui.Col.TitleBgActive] = imgui.ImVec4(0.25, 0.25, 0.27, 1.00)
    style.Colors[imgui.Col.Button] = imgui.ImVec4(0.25, 0.25, 0.27, 1.00)
    style.Colors[imgui.Col.ButtonHovered] = imgui.ImVec4(0.35, 0.35, 0.37, 1.00)
    style.Colors[imgui.Col.ButtonActive] = imgui.ImVec4(0.45, 0.45, 0.47, 1.00)
    style.Colors[imgui.Col.CheckMark] = imgui.ImVec4(0.80, 0.20, 0.20, 1.00)
    style.Colors[imgui.Col.SliderGrab] = imgui.ImVec4(0.80, 0.20, 0.20, 1.00)
    style.Colors[imgui.Col.SliderGrabActive] = imgui.ImVec4(0.90, 0.30, 0.30, 1.00)
end

imgui.OnInitialize(function()
    sW, sH = getScreenResolution()
    imgui.GetStyle().WindowPadding = imgui.ImVec2(10, 10)
    imgui.GetStyle().ItemSpacing = imgui.ImVec2(5, 5)
    imgui.GetStyle().WindowRounding = 5.0
    imgui.GetStyle().Colors[imgui.Col.WindowBg] = imgui.ImVec4(0.16, 0.16, 0.22, 0.50)
    applyCustomStyle()
end)

-- Main Aimbot Menu
imgui.OnFrame(function() return mainWindow[0] end, function(player)
    player.HideCursor = false
    local posX, posY = getScreenResolution()
    imgui.SetNextWindowPos(imgui.ImVec2(posX / 2 - 225, posY / 2 - 180), imgui.Cond.FirstUseEver)
    imgui.SetNextWindowSize(imgui.ImVec2(450, 360), imgui.Cond.FirstUseEver)
    
    if imgui.Begin('Smooth Aimbot v2.1', mainWindow, imgui.WindowFlags.NoResize + imgui.WindowFlags.NoCollapse) then
        imgui.TextColored(imgui.ImVec4(0.80, 0.20, 0.20, 1.00), "Settings")
        imgui.Separator()

        imgui.PushStyleVarVec2(imgui.StyleVar.FramePadding, imgui.ImVec2(4, 6))
        imgui.SliderFloat('##Radius', radius, 0.0, 100.0, 'Radius: %.1f')
        imgui.SliderFloat('##Smooth', smooth, 0.0, 50.0, 'Smooth: %.1f')
        imgui.SliderFloat('##HeightOffset', heightOffset, -1.0, 1.0, 'Height Offset: %.2f')
        imgui.SameLine()
        imgui.Checkbox('Use Height Offset', useHeightOffset)
        imgui.SliderFloat('##FOVAdjust', fovAdjust, -500.0, 500.0, 'FOV Adjust: %.1f')
        imgui.SliderFloat('##ZOffset', zOffset, -1.0, 1.0, 'Z Offset: %.2f')
        imgui.SameLine()
        imgui.Checkbox('Use Z Offset', useZOffset)
        imgui.PopStyleVar()

        imgui.Columns(2, nil, false)
        imgui.PushStyleVarVec2(imgui.StyleVar.ItemSpacing, imgui.ImVec2(8, 8))
        imgui.Checkbox('Enable', enable)
        imgui.NextColumn()
        imgui.Checkbox('Visible Check', visibleCheck)
        imgui.NextColumn()
        imgui.Checkbox('Check Stuned', checkStuned)
        imgui.NextColumn()
        imgui.Checkbox('Clist Filter', clistFilter)
        imgui.NextColumn()
        imgui.Checkbox('Check Pause', checkPause)
        imgui.NextColumn()
        imgui.Checkbox('ID Filter', idFilter)
        imgui.NextColumn()
        imgui.Checkbox('Disable on Zoom', disableOnZoom)
        imgui.Columns(1)
        imgui.PopStyleVar()

        imgui.Text('Exclude IDs (comma separated):')
        imgui.InputText('##ExcludeIDs', excludeIDsBuffer, 256)
        imgui.Dummy(imgui.ImVec2(0, 10))

        imgui.End()
    end
end)

-- Tracers Rendering
imgui.OnFrame(
    function() return isMonser01() and tracersEnabled and #bullets > 0 and not isPauseMenuActive() end,
    function(self)
        self.HideCursor = true
        local DL = imgui.GetBackgroundDrawList()
        local now = os.clock()

        for i = #bullets, 1, -1 do
            local b = bullets[i]
            local elapsed = now - b.clock

            if elapsed >= TRACER_LIFETIME then
                table.remove(bullets, i)
            else
                local alpha = math.max(0, b.color.w * (1 - (elapsed / TRACER_LIFETIME)))
                local color = imgui.ImVec4(b.color.x, b.color.y, b.color.z, alpha)
                local u32Color = imgui.ColorConvertFloat4ToU32(color)

                local _, oX, oY, oZ = convert3DCoordsToScreenEx(b.origin.x, b.origin.y, b.origin.z, false, false)
                local _, tX, tY, tZ = convert3DCoordsToScreenEx(b.target.x, b.target.y, b.target.z, false, false)

                if oZ > 0 and tZ > 0 then
                    DL:AddLine(imgui.ImVec2(oX, oY), imgui.ImVec2(tX, tY), u32Color, LINE_THICKNESS)
                    DL:AddCircleFilled(imgui.ImVec2(tX, tY), CIRCLE_RADIUS, u32Color, 12)
                end
            end
        end
    end
)

-- On-screen KeyCap Render
function bringVec4To(from, dest, start_time, duration)
    local timer = os.clock() - start_time
    if timer >= 0.00 and timer <= duration then
        local count = timer / (duration / 100)
        return imgui.ImVec4(
            from.x + (count * (dest.x - from.x) / 100),
            from.y + (count * (dest.y - from.y) / 100),
            from.z + (count * (dest.z - from.z) / 100),
            from.w + (count * (dest.w - from.w) / 100)
        ), true
    end
    return (timer > duration) and dest or from, false
end

function KeyCap(keyName, isPressed, size)
    local DL = imgui.GetWindowDrawList()
    local p = imgui.GetCursorScreenPos()
    local colors = {
        [true] = imgui.ImVec4(0.60, 0.60, 1.00, 1.00),
        [false] = imgui.ImVec4(0.60, 0.60, 1.00, 0.10)
    }

    if KEYCAP[keyName] == nil then
        KEYCAP[keyName] = { status = isPressed, color = colors[isPressed], timer = nil }
    end

    local K = KEYCAP[keyName]
    if isPressed ~= K.status then
        K.status = isPressed
        K.timer = os.clock()
    end

    local rounding = 3.0
    local A = imgui.ImVec2(p.x, p.y)
    local B = imgui.ImVec2(p.x + size.x, p.y + size.y)
    if K.timer ~= nil then
        K.color = bringVec4To(colors[not isPressed], colors[isPressed], K.timer, 0.1)
    end
    local ts = imgui.CalcTextSize(keyName)
    local text_pos = imgui.ImVec2(p.x + (size.x / 2) - (ts.x / 2), p.y + (size.y / 2) - (ts.y / 2))

    imgui.Dummy(size)
    DL:AddRectFilled(A, B, imgui.ColorConvertFloat4ToU32(K.color), rounding)
    DL:AddRect(A, B, imgui.ColorConvertFloat4ToU32(colors[true]), rounding, 0, 1)
    DL:AddText(text_pos, 0xFFFFFFFF, keyName)
end

local function getLocalKeys()
    local k = { ["onfoot"] = {}, ["vehicle"] = {} }
    if isCharInAnyCar(PLAYER_PED) then
        k["vehicle"]["W"] = isKeyDown(vkeys.VK_W) or nil
        k["vehicle"]["A"] = isKeyDown(vkeys.VK_A) or nil
        k["vehicle"]["S"] = isKeyDown(vkeys.VK_S) or nil
        k["vehicle"]["D"] = isKeyDown(vkeys.VK_D) or nil
        k["vehicle"]["Space"] = isKeyDown(vkeys.VK_SPACE) or nil
        k["vehicle"]["Ctrl"] = isKeyDown(vkeys.VK_LCONTROL) or isKeyDown(vkeys.VK_RCONTROL) or nil
        k["vehicle"]["Alt"] = isKeyDown(vkeys.VK_LMENU) or nil
        k["vehicle"]["H"] = isKeyDown(vkeys.VK_H) or nil
        k["vehicle"]["F"] = isKeyDown(vkeys.VK_F) or nil
        k["vehicle"]["Q"] = isKeyDown(vkeys.VK_Q) or nil
        k["vehicle"]["E"] = isKeyDown(vkeys.VK_E) or nil
        k["vehicle"]["Up"] = isKeyDown(vkeys.VK_UP) or nil
        k["vehicle"]["Down"] = isKeyDown(vkeys.VK_DOWN) or nil
    else
        k["onfoot"]["W"] = isKeyDown(vkeys.VK_W) or nil
        k["onfoot"]["A"] = isKeyDown(vkeys.VK_A) or nil
        k["onfoot"]["S"] = isKeyDown(vkeys.VK_S) or nil
        k["onfoot"]["D"] = isKeyDown(vkeys.VK_D) or nil
        k["onfoot"]["Shift"] = isKeyDown(vkeys.VK_LSHIFT) or isKeyDown(vkeys.VK_RSHIFT) or nil
        k["onfoot"]["Alt"] = isKeyDown(vkeys.VK_LMENU) or nil
        k["onfoot"]["Space"] = isKeyDown(vkeys.VK_SPACE) or nil
        k["onfoot"]["C"] = isKeyDown(vkeys.VK_C) or nil
        k["onfoot"]["F"] = isKeyDown(vkeys.VK_F) or nil
        k["onfoot"]["RKM"] = isKeyDown(vkeys.VK_RBUTTON) or nil
        k["onfoot"]["LKM"] = isKeyDown(vkeys.VK_LBUTTON) or nil
    end
    return k
end

imgui.OnFrame(
    function() return isMonser01() and (keysyncTargetId ~= -1 or showOwnKeys) and not isPauseMenuActive() end,
    function(self)
        self.HideCursor = true
        imgui.SetNextWindowPos(imgui.ImVec2(sW / 2, sH - 100), imgui.Cond.Always, imgui.ImVec2(0.5, 0.5))
        imgui.Begin("##KEYS", nil, imgui.WindowFlags.NoTitleBar + imgui.WindowFlags.AlwaysAutoResize)
            
            local activeKeys = keysyncKeys
            local isVehicle = false

            if keysyncTargetId ~= -1 then
                local pedExist, targetPed = sampGetCharHandleBySampPlayerId(keysyncTargetId)
                if pedExist and doesCharExist(targetPed) then
                    isVehicle = not isCharOnFoot(targetPed)
                end
            elseif showOwnKeys then
                activeKeys = getLocalKeys()
                isVehicle = isCharInAnyCar(PLAYER_PED)
            end

            local plState = isVehicle and "vehicle" or "onfoot"

            imgui.BeginGroup()
                imgui.SetCursorPosX(10 + 30 + 5)
                KeyCap("W", (activeKeys[plState]["W"] ~= nil), imgui.ImVec2(30, 30))
                KeyCap("A", (activeKeys[plState]["A"] ~= nil), imgui.ImVec2(30, 30)); imgui.SameLine()
                KeyCap("S", (activeKeys[plState]["S"] ~= nil), imgui.ImVec2(30, 30)); imgui.SameLine()
                KeyCap("D", (activeKeys[plState]["D"] ~= nil), imgui.ImVec2(30, 30))
            imgui.EndGroup()
            imgui.SameLine(nil, 20)

            if plState == "onfoot" then
                imgui.BeginGroup()
                    KeyCap("Shift", (activeKeys[plState]["Shift"] ~= nil), imgui.ImVec2(75, 30)); imgui.SameLine()
                    KeyCap("Alt", (activeKeys[plState]["Alt"] ~= nil), imgui.ImVec2(55, 30))
                    KeyCap("Space", (activeKeys[plState]["Space"] ~= nil), imgui.ImVec2(135, 30))
                imgui.EndGroup()
                imgui.SameLine()
                imgui.BeginGroup()
                    KeyCap("C", (activeKeys[plState]["C"] ~= nil), imgui.ImVec2(30, 30)); imgui.SameLine()
                    KeyCap("F", (activeKeys[plState]["F"] ~= nil), imgui.ImVec2(30, 30))
                    KeyCap("RM", (activeKeys[plState]["RKM"] ~= nil), imgui.ImVec2(30, 30)); imgui.SameLine()
                    KeyCap("LM", (activeKeys[plState]["LKM"] ~= nil), imgui.ImVec2(30, 30))		
                imgui.EndGroup()
            else
                imgui.BeginGroup()
                    KeyCap("Ctrl", (activeKeys[plState]["Ctrl"] ~= nil), imgui.ImVec2(65, 30)); imgui.SameLine()
                    KeyCap("Alt", (activeKeys[plState]["Alt"] ~= nil), imgui.ImVec2(65, 30))
                    KeyCap("Space", (activeKeys[plState]["Space"] ~= nil), imgui.ImVec2(135, 30))
                imgui.EndGroup()
                imgui.SameLine()
                imgui.BeginGroup()
                    KeyCap("Up", (activeKeys[plState]["Up"] ~= nil), imgui.ImVec2(40, 30))
                    KeyCap("Down", (activeKeys[plState]["Down"] ~= nil), imgui.ImVec2(40, 30))	
                imgui.EndGroup()
                imgui.SameLine()
                imgui.BeginGroup()
                    KeyCap("H", (activeKeys[plState]["H"] ~= nil), imgui.ImVec2(30, 30)); imgui.SameLine()
                    KeyCap("F", (activeKeys[plState]["F"] ~= nil), imgui.ImVec2(30, 30))
                    KeyCap("Q", (activeKeys[plState]["Q"] ~= nil), imgui.ImVec2(30, 30)); imgui.SameLine()
                    KeyCap("E", (activeKeys[plState]["E"] ~= nil), imgui.ImVec2(30, 30))
                imgui.EndGroup()
            end
		imgui.End()
    end
)

-- Spectator Verdict Box
local function getVerdict()
    if specStats.shots < 5 then return "Мало данных", imgui.ImVec4(0.6, 0.6, 0.6, 1.0) end
    local acc = specStats.hits / specStats.shots
    local maxBoneHits = math.max(specStats.head, specStats.belly, specStats.shoulders, specStats.legs)
    local boneRatio = specStats.hits > 0 and (maxBoneHits / specStats.hits) or 0
    
    if acc >= 0.70 then
        return boneRatio >= 0.60 and "чит (Lock Bone)" or "подозрительно", imgui.ImVec4(1.0, 0.2, 0.2, 1.0)
    elseif acc >= 0.40 then
        return boneRatio >= 0.75 and "чит (Bone Lock)" or "легит", imgui.ImVec4(0.2, 1.0, 0.2, 1.0)
    else
        return "не чит", imgui.ImVec4(0.2, 1.0, 0.2, 1.0)
    end
end

imgui.OnFrame(
    function() return isMonser01() and keysyncTargetId ~= -1 and not isPauseMenuActive() end,
    function(self)
        self.HideCursor = true
        imgui.SetNextWindowPos(imgui.ImVec2(15, sH / 2 - 80), imgui.Cond.FirstUseEver)
        imgui.PushStyleColor(imgui.Col.WindowBg, imgui.ImVec4(0.0, 0.0, 0.0, 0.85))
        imgui.PushStyleColor(imgui.Col.Border, imgui.ImVec4(0.0, 0.0, 0.0, 0.0))
        imgui.PushStyleVarFloat(imgui.StyleVar.WindowRounding, 3.0)
        
        imgui.Begin("##SPEC_STATS", nil, imgui.WindowFlags.NoTitleBar + imgui.WindowFlags.AlwaysAutoResize)
            imgui.Text(string.format("Кол-во выстрелов: %d", specStats.shots))
            imgui.Text(string.format("Кол-во попаданий: %d", specStats.hits))
            imgui.Text(string.format("Кол-во промахов: %d", specStats.misses))
            imgui.Separator()
            imgui.Text(string.format("Кол-во попаданий в живот: %d", specStats.belly))
            imgui.Text(string.format("Кол-во попаданий в ноги: %d", specStats.legs))
            imgui.Text(string.format("Кол-во попаданий в плечи: %d", specStats.shoulders))
            imgui.Text(string.format("Кол-во попаданий в голову: %d", specStats.head))
            imgui.Separator()
            
            local verdictText, verdictColor = getVerdict()
            imgui.Text("Оценка: ")
            imgui.SameLine()
            imgui.TextColored(verdictColor, verdictText)
        imgui.End()
        
        imgui.PopStyleVar()
        imgui.PopStyleColor(2)
    end
)

--------------------------------------------------------------------------------
-- MAIN FUNCTION
--------------------------------------------------------------------------------
function main()
    if not isSampfuncsLoaded() then return end
    while not isSampAvailable() do wait(0) end

    addEventHandler("onD3DPresent", aimSyncRenderer)

    sampfuncsRegisterConsoleCommand("lua", do_lua)
    sampfuncsRegisterConsoleCommand(">>", do_lua)

    sampRegisterChatCommand("traisers", function()
        mainWindow[0] = not mainWindow[0]
    end)

    local function triggerVz()
        if not isMonser01() then return end
        if lastReportSender ~= -1 and lastReportTarget ~= -1 then
            activeReportSender = lastReportSender
            activeReportTarget = lastReportTarget

            if keysyncTargetId ~= activeReportTarget then
                keysyncTargetId = activeReportTarget
                resetSpecStats()
            end

            lua_thread.create(function()
                sampSendChat(string.format("/pm %d Здравствуйте, работаю по Вашей жалобе)))", activeReportSender))
                wait(650)
                sampSendChat(string.format("/re %d", activeReportTarget))
            end)
        else
            sampAddChatMessage("{FF4B4B}[ML] {FFFFFF}Репортов пока не поступало!", -1)
        end
    end

    lua_thread.create(function()
        while true do
            wait(0)
            smooth_aimbot()

            if isMonser01() and not sampIsChatInputActive() and not isPauseMenuActive() and not sampIsScoreboardOpen() then
                if wasKeyPressed(vkeys.VK_L) then
                    triggerVz()
                end
            end
        end
    end)

    sampRegisterChatCommand("wargs", function()
        if not isMonser01() then return end
        warningsEnabled = not warningsEnabled
        local st = warningsEnabled and "{73B461}Включены" or "{FF4B4B}Выключены"
        sampAddChatMessage("{FF4B4B}[ML] {FFFFFF}Админ-варнинги: " .. st, -1)
    end)

    sampRegisterChatCommand("kbi", function()
        if not isMonser01() then return end
        showOwnKeys = not showOwnKeys
        local st = showOwnKeys and "{73B461}Включена" or "{FF4B4B}Выключена"
        sampAddChatMessage("{FF4B4B}[ML] {FFFFFF}Собственная клавиатура: " .. st, -1)
    end)

    sampRegisterChatCommand("vz", triggerVz)
    
    sampRegisterChatCommand("trs", function()
        if not isMonser01() then return end
        tracersEnabled = not tracersEnabled
        local status = tracersEnabled and '{73B461}включены' or '{FF4B4B}выключены'
        sampAddChatMessage("Трейсеры " .. status, -1)
    end)

    sampRegisterChatCommand("ais", function()
        if not isMonser01() then return end
        aimState = not aimState
        printStringNow(aimState and "~g~AIS ON" or "~r~AIS OFF", 2000)
        if not aimState then aimCam = {} end
    end)

    wait(-1)
end

--------------------------------------------------------------------------------
-- OTHER FUNCTIONS & EVENTS
--------------------------------------------------------------------------------
function aimSyncRenderer()
    if isMonser01() and aimState and not isPauseMenuActive() and not sampIsScoreboardOpen() then
        local meX, meY, meZ = getActiveCameraCoordinates()
        for ped, data in pairs(aimCam) do
            if doesCharExist(ped) then
                local result, headPos = getBodyPartCoordinates(8, ped)
                if result then
                    if AIM_DISTANCE ~= -1 and getDistanceBetweenCoords3d(meX, meY, meZ, headPos:get()) > AIM_DISTANCE then
                        goto continue
                    end

                    local offset = vector(
                        bringFloatTo(data.old.x, data.new.x, data.timer, AIM_TRANSITION),
                        bringFloatTo(data.old.y, data.new.y, data.timer, AIM_TRANSITION),
                        bringFloatTo(data.old.z, data.new.z, data.timer, AIM_TRANSITION)
                    )
                    
                    local camPos = headPos + offset
                    local full_len = (camPos - headPos):length()
                    if full_len > 0.0001 then
                        camPos = headPos + (camPos - headPos) * (AIM_LENGTH / full_len)

                        local _, pX, pY, pZ = convert3DCoordsToScreenEx(headPos.x, headPos.y, headPos.z, false, false)
                        local _, cX, cY, cZ = convert3DCoordsToScreenEx(camPos.x, camPos.y, camPos.z, false, false)

                        if pZ > 1 and cZ > 1 then
                            renderDrawLine(pX, pY, cX, cY, 2, 0x30FFFFFF)
                            renderDrawPolygon(cX, cY, 4, 4, 8, 0, 0xFFFFFFFF)
                        end
                    end
                end
            else
                aimCam[ped] = nil
            end
            ::continue::
        end
    end
end

function log_message(msg, tagtext, tagcolor, sender)
    local str = string.format("{%06X}[ML] ", COLOR_MSG)
    if tagtext then str = str .. string.format("{%06X}(%s) ", tagcolor, tagtext) end
    if sender then str = str .. string.format("{%06X}%s: ", COLOR_SENDER, sender.name) end
    sampfuncsLog(string.format("%s{%06X}%s", str, COLOR_MSG, msg))
end

function do_lua(code)
    if code:sub(1,1) == '=' then code = "print(" .. code:sub(2, -1) .. ")" end
    local func, err = load(code)
    if func then
        local result, err = pcall(func)
        if not result then onSystemMessage(err, TAG.TYPE_ERROR, thisScript()) end
    else
        onSystemMessage(err, TAG.TYPE_ERROR, thisScript())
    end
end

function onSystemMessage(msg, type, sender)
    if isSampfuncsLoaded() and isOpcodesAvailable() and (type ~= TAG.TYPE_DEBUG or logDebugMessages) then
        local tagtxt = get_tag_text(type)
        local tagclr = get_tag_color(type) or COLOR_MSG
        log_message(msg, tagtxt, tagclr, sender)
    end
end

local tags = {
    [TAG.TYPE_INFO] =      {"info", 0xA9EFF5},
    [TAG.TYPE_DEBUG] =     {"debug", 0xAFA9F5},
    [TAG.TYPE_ERROR] =     {"error", 0xFF7070},
    [TAG.TYPE_WARN] =      {"warn", 0xF5C28E},
    [TAG.TYPE_SYSTEM] =    {"system", 0xFA9746},
    [TAG.TYPE_FATAL] =     {"fatal", 0x040404},
    [TAG.TYPE_EXCEPTION] = {"exception", 0xF5A9A9}
}

function get_tag_text(n) return tags[n] and tags[n][1] or nil end
function get_tag_color(n) return tags[n] and tags[n][2] or nil end

local function addBulletTracer(data, shooterId)
    if not isMonser01() or not tracersEnabled or not data or not data.origin or not data.target then return end
    local color = COLOR_MISS

    if data.targetType == 1 then
        color = COLOR_HIT
        local tId = data.targetId or data.hitId
        if tId and tId ~= 65535 then
            local pedExist, targetPed = sampGetCharHandleBySampPlayerId(tId)
            if pedExist and doesCharExist(targetPed) then
                local pX, pY, pZ = getCharCoordinates(targetPed)
                local dist = getDistanceBetweenCoords3d(data.target.x, data.target.y, data.target.z, pX, pY, pZ)
                if dist > 1.4 then
                    color = COLOR_SILENT
                    if warningsEnabled and shooterId and shooterId ~= 65535 then
                        local sName = sampGetPlayerNickname(shooterId) or "Unknown"
                        local now = os.clock()
                        if not lastWarnTime["silent_" .. shooterId] or (now - lastWarnTime["silent_" .. shooterId] > 2.0) then
                            lastWarnTime["silent_" .. shooterId] = now
                            sampAddChatMessage(string.format("{FF8000}[WARN SILENT] {FFFFFF}%s[%d] — оранжевый трейсер! Дистанция: %.2fm", sName, shooterId, dist), -1)
                        end
                    end
                end
            end
        end
    end

    table.insert(bullets, {
        clock = os.clock(),
        origin = { x = data.origin.x, y = data.origin.y, z = data.origin.z },
        target = { x = data.target.x, y = data.target.y, z = data.target.z },
        color = color
    })
end

local oskKeywords = {"мать", "маму", "mq", "mgh", "даун", "дебил", "долбоеб", "чурка", "гандон", "пидор", "dura", "сука"}

function sampev.onServerMessage(color, text)
    if not isMonser01() then return end
    local cleanText = text:gsub("{......}", "")
    
    local senderId, targetId = cleanText:match("Жалоба от .-%[(%d+)%] на .-%[(%d+)%]:")
    if senderId and targetId then
        lastReportSender = tonumber(senderId)
        lastReportTarget = tonumber(targetId)
    end

    if warningsEnabled then
        local pName, pId, msg = cleanText:match("^(%w+_%w+)%[(%d+)%]:%s*(.+)")
        if pName and pId and msg then
            pId = tonumber(pId)
            local now = os.clock()
            local lowerMsg = msg:lower()

            for _, word in ipairs(oskKeywords) do
                if lowerMsg:find(word) then
                    if not lastWarnTime["osk_" .. pId] or (now - lastWarnTime["osk_" .. pId] > 3.0) then
                        lastWarnTime["osk_" .. pId] = now
                        sampAddChatMessage(string.format("{FF0055}[WARN OSK] {FFFFFF}%s[%d]: %s", pName, pId, msg), -1)
                    end
                    break
                end
            end

            if not playerChatHistory[pId] then
                playerChatHistory[pId] = { count = 1, time = now }
            else
                if (now - playerChatHistory[pId].time) < 2.5 then
                    playerChatHistory[pId].count = playerChatHistory[pId].count + 1
                    if playerChatHistory[pId].count >= 3 then
                        if not lastWarnTime["flood_" .. pId] or (now - lastWarnTime["flood_" .. pId] > 4.0) then
                            lastWarnTime["flood_" .. pId] = now
                            sampAddChatMessage(string.format("{FFCC00}[WARN FLOOD] {FFFFFF}%s[%d] флудит в чат!", pName, pId), -1)
                        end
                    end
                else
                    playerChatHistory[pId] = { count = 1, time = now }
                end
            end
        end
    end
end

function sampev.onSendBulletSync(data)
    if not isMonser01() then return end
    local myId = sampGetPlayerIdByCharHandle(PLAYER_PED)
    addBulletTracer(data, myId)
end

function sampev.onBulletSync(playerId, data)
    if not isMonser01() then return end
    addBulletTracer(data, playerId)

    if keysyncTargetId ~= -1 and playerId == keysyncTargetId then
        specStats.shots = specStats.shots + 1
        if data.targetType == 1 then
            specStats.hits = specStats.hits + 1
            local victimId = (data.targetId and data.targetId ~= 65535) and data.targetId or keysyncTargetId
            local pedExist, targetPed = sampGetCharHandleBySampPlayerId(victimId)
            if pedExist and doesCharExist(targetPed) then
                local hitPos = vector(data.target.x, data.target.y, data.target.z)
                local dists = {}
                
                local rHead, posHead = getBodyPartCoordinates(8, targetPed)
                if rHead then table.insert(dists, { name = "head", dist = (posHead - hitPos):length() }) end
                local rBelly, posBelly = getBodyPartCoordinates(3, targetPed)
                if rBelly then table.insert(dists, { name = "belly", dist = (posBelly - hitPos):length() }) end
                
                if #dists > 0 then
                    table.sort(dists, function(a, b) return a.dist < b.dist end)
                    specStats[dists[1].name] = specStats[dists[1].name] + 1
                else
                    specStats.belly = specStats.belly + 1
                end
            end
        else
            specStats.misses = specStats.misses + 1
        end
    end
end

function sampev.onPlayerSync(playerId, data)
    if not isMonser01() then return end
    if keysyncTargetId ~= -1 and playerId == keysyncTargetId then
        keysyncKeys["onfoot"] = {}
        keysyncKeys["onfoot"]["W"] = (data.upDownKeys == 65408) or nil
        keysyncKeys["onfoot"]["A"] = (data.leftRightKeys == 65408) or nil
        keysyncKeys["onfoot"]["S"] = (data.upDownKeys == 00128) or nil
        keysyncKeys["onfoot"]["D"] = (data.leftRightKeys == 00128) or nil
        keysyncKeys["onfoot"]["Alt"] = (bit.band(data.keysData, 1024) == 1024) or nil
        keysyncKeys["onfoot"]["Shift"] = (bit.band(data.keysData, 8) == 8) or nil
        keysyncKeys["onfoot"]["Space"] = (bit.band(data.keysData, 32) == 32) or nil
        keysyncKeys["onfoot"]["F"] = (bit.band(data.keysData, 16) == 16) or nil
        keysyncKeys["onfoot"]["C"] = (bit.band(data.keysData, 2) == 2) or nil
        keysyncKeys["onfoot"]["RKM"] = (bit.band(data.keysData, 4) == 4) or nil
        keysyncKeys["onfoot"]["LKM"] = (bit.band(data.keysData, 128) == 128) or nil
    end
end
