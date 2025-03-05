-- Nova PNG Library (Exploit Environment Compatible)
-- A LuaU implementation for Roblox that downloads a PNG from a URL,
-- decodes it (including a basic deflate implementation supporting stored,
-- fixed, and dynamic Huffman blocks), and renders it as a grid of pixel Frames.
-- This version is adjusted for exploit environments (e.g. Synapse X) by checking for
-- available HTTP request functions.
--
-- Usage:
--    local NovaPNG = require(path.to.NovaPNG)
--    NovaPNG.Load("https://example.com/image.png", parentGuiObject, pixelSize)

local NovaPNG = {}

-----------------------
-- HTTP Request Helper
-----------------------
local function httpRequest(url)
    if syn and syn.request then
        local response = syn.request({
            Url = url,
            Method = "GET"
        })
        if response.StatusCode ~= 200 then
            error("HTTP request failed with status code: " .. tostring(response.StatusCode))
        end
        return response.Body
    elseif http and http.request then
        local response = http.request(url)
        if not response or not response.Body then
            error("HTTP request failed using http.request")
        end
        return response.Body
    else
        local HttpService = game:GetService("HttpService")
        return HttpService:GetAsync(url)
    end
end

-----------------------
-- BitStream Utility --
-----------------------
local BitStream = {}
BitStream.__index = BitStream
function BitStream.new(data)
    local self = setmetatable({}, BitStream)
    self.data = data
    self.pos = 1
    self.bitBuffer = 0
    self.bitCount = 0
    return self
end
function BitStream:readBits(n)
    local result = 0
    local bitsRead = 0
    while n > 0 do
        if self.bitCount == 0 then
            if self.pos > #self.data then error("Attempt to read past end of data") end
            self.bitBuffer = string.byte(self.data, self.pos)
            self.pos = self.pos + 1
            self.bitCount = 8
        end
        local take = math.min(n, self.bitCount)
        result = result + ((self.bitBuffer % (2 ^ take)) * (2 ^ bitsRead))
        self.bitBuffer = math.floor(self.bitBuffer / (2 ^ take))
        self.bitCount = self.bitCount - take
        n = n - take
        bitsRead = bitsRead + take
    end
    return result
end
function BitStream:align()
    self.bitCount = 0
end
function BitStream:readByte()
    if self.pos > #self.data then error("Attempt to read past end of data") end
    local byte = string.byte(self.data, self.pos)
    self.pos = self.pos + 1
    return byte
end
function BitStream:readBytes(n)
    local bytes = self.data:sub(self.pos, self.pos + n - 1)
    self.pos = self.pos + n
    return bytes
end

-----------------------------
-- Huffman Tree Functions  --
-----------------------------
local bit32 = bit32 or _G.bit32
local function buildHuffmanTree(lengths)
    local tree = {}
    local codes = {}
    local bl_count = {}
    local maxLen = 0
    for symbol, len in pairs(lengths) do
        if len > maxLen then maxLen = len end
        bl_count[len] = (bl_count[len] or 0) + 1
    end
    local next_code = {}
    local code = 0
    for bits = 1, maxLen do
        code = (code + (bl_count[bits - 1] or 0)) * 2
        next_code[bits] = code
    end
    for symbol, len in pairs(lengths) do
        if len ~= 0 then
            local assigned = next_code[len]
            next_code[len] = next_code[len] + 1
            codes[symbol] = {code = assigned, length = len}
        end
    end
    for symbol, info in pairs(codes) do
        local code = info.code
        local length = info.length
        local node = tree
        for i = length - 1, 0, -1 do
            local bit = bit32.rshift(code, i) % 2
            if not node[bit] then
                node[bit] = {}
            end
            node = node[bit]
        end
        node.symbol = symbol
    end
    return tree
end

local function decodeSymbol(bs, tree)
    local node = tree
    while node.symbol == nil do
        local bit = bs:readBits(1)
        node = node[bit]
        if not node then error("Invalid Huffman code") end
    end
    return node.symbol
end

------------------------------------
-- Deflate (Inflate) Implementation --
------------------------------------
local lengthExtra = {
    [257] = {base = 3, extra = 0},
    [258] = {base = 4, extra = 0},
    [259] = {base = 5, extra = 0},
    [260] = {base = 6, extra = 0},
    [261] = {base = 7, extra = 0},
    [262] = {base = 8, extra = 0},
    [263] = {base = 9, extra = 0},
    [264] = {base = 10, extra = 0},
    [265] = {base = 11, extra = 1},
    [266] = {base = 13, extra = 1},
    [267] = {base = 15, extra = 1},
    [268] = {base = 17, extra = 1},
    [269] = {base = 19, extra = 2},
    [270] = {base = 23, extra = 2},
    [271] = {base = 27, extra = 2},
    [272] = {base = 31, extra = 2},
    [273] = {base = 35, extra = 3},
    [274] = {base = 43, extra = 3},
    [275] = {base = 51, extra = 3},
    [276] = {base = 59, extra = 3},
    [277] = {base = 67, extra = 4},
    [278] = {base = 83, extra = 4},
    [279] = {base = 99, extra = 4},
    [280] = {base = 115, extra = 4},
    [281] = {base = 131, extra = 5},
    [282] = {base = 163, extra = 5},
    [283] = {base = 195, extra = 5},
    [284] = {base = 227, extra = 5},
    [285] = {base = 258, extra = 0},
}
local distanceExtra = {
    [0]  = {base = 1, extra = 0},
    [1]  = {base = 2, extra = 0},
    [2]  = {base = 3, extra = 0},
    [3]  = {base = 4, extra = 0},
    [4]  = {base = 5, extra = 1},
    [5]  = {base = 7, extra = 1},
    [6]  = {base = 9, extra = 2},
    [7]  = {base = 13, extra = 2},
    [8]  = {base = 17, extra = 3},
    [9]  = {base = 25, extra = 3},
    [10] = {base = 33, extra = 4},
    [11] = {base = 49, extra = 4},
    [12] = {base = 65, extra = 5},
    [13] = {base = 97, extra = 5},
    [14] = {base = 129, extra = 6},
    [15] = {base = 193, extra = 6},
    [16] = {base = 257, extra = 7},
    [17] = {base = 385, extra = 7},
    [18] = {base = 513, extra = 8},
    [19] = {base = 769, extra = 8},
    [20] = {base = 1025, extra = 9},
    [21] = {base = 1537, extra = 9},
    [22] = {base = 2049, extra = 10},
    [23] = {base = 3073, extra = 10},
    [24] = {base = 4097, extra = 11},
    [25] = {base = 6145, extra = 11},
    [26] = {base = 8193, extra = 12},
    [27] = {base = 12289, extra = 12},
    [28] = {base = 16385, extra = 13},
    [29] = {base = 24577, extra = 13},
}

local function decodeLength(symbol, bs)
    local info = lengthExtra[symbol]
    if not info then error("Invalid length symbol: " .. symbol) end
    local extra = bs:readBits(info.extra)
    return info.base + extra
end
local function decodeDistance(symbol, bs)
    local info = distanceExtra[symbol]
    if not info then error("Invalid distance symbol: " .. symbol) end
    local extra = bs:readBits(info.extra)
    return info.base + extra
end

local function buildFixedLitLenTree()
    local lengths = {}
    for i = 0, 287 do
        if i <= 143 then
            lengths[i] = 8
        elseif i <= 255 then
            lengths[i] = 9
        elseif i <= 279 then
            lengths[i] = 7
        else
            lengths[i] = 8
        end
    end
    return buildHuffmanTree(lengths)
end
local function buildFixedDistTree()
    local lengths = {}
    for i = 0, 29 do
        lengths[i] = 5
    end
    return buildHuffmanTree(lengths)
end

local function buildDynamicTrees(bs)
    local HLIT = bs:readBits(5) + 257
    local HDIST = bs:readBits(5) + 1
    local HCLEN = bs:readBits(4) + 4
    local codeLengthOrder = {16,17,18,0,8,7,9,6,10,5,11,4,12,3,13,2,14,1,15}
    local codeLengthCodes = {}
    for i = 0, 18 do
        codeLengthCodes[i] = 0
    end
    for i = 0, HCLEN - 1 do
        codeLengthCodes[codeLengthOrder[i+1]] = bs:readBits(3)
    end
    local codeLengthTree = buildHuffmanTree(codeLengthCodes)
    local totalCodes = HLIT + HDIST
    local codeLengths = {}
    local i = 0
    while i < totalCodes do
        local symbol = decodeSymbol(bs, codeLengthTree)
        if symbol < 16 then
            codeLengths[i] = symbol
            i = i + 1
        elseif symbol == 16 then
            if i == 0 then error("No previous code length for repeat") end
            local repeatCount = bs:readBits(2) + 3
            local prev = codeLengths[i-1]
            for j = 1, repeatCount do
                codeLengths[i] = prev
                i = i + 1
            end
        elseif symbol == 17 then
            local repeatCount = bs:readBits(3) + 3
            for j = 1, repeatCount do
                codeLengths[i] = 0
                i = i + 1
            end
        elseif symbol == 18 then
            local repeatCount = bs:readBits(7) + 11
            for j = 1, repeatCount do
                codeLengths[i] = 0
                i = i + 1
            end
        else
            error("Invalid symbol in dynamic Huffman code lengths: " .. symbol)
        end
    end
    local litLenLengths = {}
    local distLengths = {}
    for j = 0, HLIT - 1 do
        litLenLengths[j] = codeLengths[j] or 0
    end
    for j = 0, HDIST - 1 do
        distLengths[j] = codeLengths[HLIT + j] or 0
    end
    local litLenTree = buildHuffmanTree(litLenLengths)
    local distTree = buildHuffmanTree(distLengths)
    return litLenTree, distTree
end

local function decodeCompressedBlock(bs, litLenTree, distTree, out)
    while true do
        local symbol = decodeSymbol(bs, litLenTree)
        if symbol < 256 then
            out[#out+1] = symbol
        elseif symbol == 256 then
            break
        else
            local length = decodeLength(symbol, bs)
            local distSymbol = decodeSymbol(bs, distTree)
            local distance = decodeDistance(distSymbol, bs)
            local outLen = #out
            local startPos = outLen - distance + 1
            if startPos < 1 then error("Invalid distance") end
            for i = 1, length do
                out[#out+1] = out[startPos + i - 1]
            end
        end
    end
end

local function inflate(zlibData)
    if #zlibData < 6 then error("Invalid zlib data") end
    local header = zlibData:sub(1,2)
    local compressed = zlibData:sub(3, #zlibData - 4)
    local bs = BitStream.new(compressed)
    local out = {}
    while true do
        local bfinal = bs:readBits(1)
        local btype = bs:readBits(2)
        if btype == 0 then
            bs:align()
            local len = bs:readByte() + bs:readByte() * 256
            local nlen = bs:readByte() + bs:readByte() * 256
            if len ~= ((bit32.bnot(nlen)) & 0xFFFF) then error("Stored block length check failed") end
            local blockData = bs:readBytes(len)
            for i = 1, #blockData do
                out[#out+1] = string.byte(blockData, i)
            end
        elseif btype == 1 or btype == 2 then
            local litLenTree, distTree
            if btype == 1 then
                litLenTree = buildFixedLitLenTree()
                distTree = buildFixedDistTree()
            else
                litLenTree, distTree = buildDynamicTrees(bs)
            end
            decodeCompressedBlock(bs, litLenTree, distTree, out)
        else
            error("Invalid block type: " .. btype)
        end
        if bfinal == 1 then break end
    end
    return string.char(table.unpack(out))
end

-------------------------
-- PNG Parsing & Decoding --
-------------------------
local function readUInt32(data, pos)
    local a, b, c, d = string.byte(data, pos, pos+3)
    return a * 16777216 + b * 65536 + c * 256 + d
end

local function parseIHDR(chunkData)
    local width = readUInt32(chunkData, 1)
    local height = readUInt32(chunkData, 5)
    local bitDepth = string.byte(chunkData, 9)
    local colorType = string.byte(chunkData, 10)
    local compression = string.byte(chunkData, 11)
    local filter = string.byte(chunkData, 12)
    local interlace = string.byte(chunkData, 13)
    if bitDepth ~= 8 then
        error("Only 8-bit depth PNGs are supported")
    end
    if colorType ~= 2 then
        error("Only truecolor (RGB) PNGs are supported")
    end
    if compression ~= 0 then
        error("Unknown compression method")
    end
    if interlace ~= 0 then
        error("Interlaced PNGs are not supported")
    end
    return {
        width = width,
        height = height,
        bitDepth = bitDepth,
        colorType = colorType,
        compression = compression,
        filter = filter,
        interlace = interlace
    }
end

local function applyFilters(data, width, height, bpp)
    local stride = width * bpp
    local pos = 1
    local result = {}
    for y = 1, height do
        local filterType = string.byte(data, pos)
        pos = pos + 1
        local scanline = { string.byte(data, pos, pos + stride - 1) }
        pos = pos + stride
        if filterType == 0 then
            -- No filter.
        elseif filterType == 1 then
            for i = 1, #scanline do
                local a = (i > bpp) and scanline[i - bpp] or 0
                scanline[i] = (scanline[i] + a) % 256
            end
        elseif filterType == 2 then
            local prev = result[y - 1] or {}
            for i = 1, #scanline do
                local b = prev[i] or 0
                scanline[i] = (scanline[i] + b) % 256
            end
        elseif filterType == 3 then
            local prev = result[y - 1] or {}
            for i = 1, #scanline do
                local a = (i > bpp) and scanline[i - bpp] or 0
                local b = prev[i] or 0
                scanline[i] = (scanline[i] + math.floor((a + b) / 2)) % 256
            end
        elseif filterType == 4 then
            local prev = result[y - 1] or {}
            for i = 1, #scanline do
                local a = (i > bpp) and scanline[i - bpp] or 0
                local b = prev[i] or 0
                local c = (i > bpp and prev[i - bpp]) or 0
                local p = a + b - c
                local pa = math.abs(p - a)
                local pb = math.abs(p - b)
                local pc = math.abs(p - c)
                local pr = (pa <= pb and pa <= pc) and a or (pb <= pc and b or c)
                scanline[i] = (scanline[i] + pr) % 256
            end
        else
            error("Unsupported filter type: " .. filterType)
        end
        result[y] = scanline
    end
    return result
end

local function decodePNG(data)
    if data:sub(1, 8) ~= "\137PNG\r\n\26\n" then
        error("Not a valid PNG file")
    end
    local pos = 9
    local ihdr = nil
    local idatChunks = {}
    while pos <= #data do
        local length = readUInt32(data, pos)
        pos = pos + 4
        local chunkType = data:sub(pos, pos + 3)
        pos = pos + 4
        local chunkData = data:sub(pos, pos + length - 1)
        pos = pos + length
        local crc = data:sub(pos, pos + 3)
        pos = pos + 4
        if chunkType == "IHDR" then
            ihdr = parseIHDR(chunkData)
        elseif chunkType == "IDAT" then
            table.insert(idatChunks, chunkData)
        elseif chunkType == "IEND" then
            break
        end
    end
    if not ihdr then error("PNG missing IHDR chunk") end
    local compressedData = table.concat(idatChunks)
    local decompressed = inflate(compressedData)
    local pixelData = applyFilters(decompressed, ihdr.width, ihdr.height, 3)
    return {
        width = ihdr.width,
        height = ihdr.height,
        pixels = pixelData
    }
end

-------------------------
-- Rendering Function  --
-------------------------
function NovaPNG.Render(bitmap, parent, pixelSize)
    pixelSize = pixelSize or 1
    local container = Instance.new("Frame")
    container.Size = UDim2.new(0, bitmap.width * pixelSize, 0, bitmap.height * pixelSize)
    container.BackgroundTransparency = 1
    container.Parent = parent
    for y = 1, bitmap.height do
        local scanline = bitmap.pixels[y]
        for x = 1, bitmap.width do
            local baseIndex = (x - 1) * 3
            local r = scanline[baseIndex + 1]
            local g = scanline[baseIndex + 2]
            local b = scanline[baseIndex + 3]
            local pixelFrame = Instance.new("Frame")
            pixelFrame.Size = UDim2.new(0, pixelSize, 0, pixelSize)
            pixelFrame.Position = UDim2.new(0, (x - 1) * pixelSize, 0, (y - 1) * pixelSize)
            pixelFrame.BackgroundColor3 = Color3.fromRGB(r, g, b)
            pixelFrame.BorderSizePixel = 0
            pixelFrame.Parent = container
        end
    end
    return container
end

-------------------------
-- Main Loader Function --
-------------------------
function NovaPNG.Load(url, parent, pixelSize)
    local data = httpRequest(url)
    local bitmap = decodePNG(data)
    return NovaPNG.Render(bitmap, parent, pixelSize)
end

return NovaPNG
