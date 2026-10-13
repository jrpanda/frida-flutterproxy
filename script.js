/* Global variables */
var appId = null;
var appId_iOS = null;

var BURP_PROXY_IP = "null";   // "YOUR_IP"
var BURP_PROXY_PORT = null; // YOUR_PORT

var flutter_base = null;
var flutter_size = null;

var PT_LOAD_rodata_p_memsz = null;
var PT_LOAD_text_p_vaddr = null;
var PT_LOAD_text_p_memsz = null;
var PT_GNU_RELRO_p_vaddr = null;
var PT_GNU_RELRO_p_memsz = null;

var TEXT_segment_text_section_offset = null;
var TEXT_segment_text_section_size = null;
var TEXT_segment_cstring_section_offset = null;
var TEXT_segment_cstring_section_size = null;
var DATA_segment_const_section_offset = null;
var DATA_segment_const_section_size = null;

var ssl_client_string_pattern_found_addr = null;
var verify_cert_chain_func_addr = null;
var handshake_string_pattern_found_addr = null;
var verify_peer_cert_func_addr = null;

var Socket_CreateConnect_string_pattern_found_addr = null;
var Socket_CreateConnect_func_addr = null;

var GetSockAddr_func_addr = null;
var sockaddr = null;
/* Global variables */

/* Util functions */
// Find application package name
function findAppId() {
    if (Process.platform === "linux") {
        var pm = Java.use('android.app.ActivityThread').currentApplication();
        return pm.getApplicationContext().getPackageName();
    } else {
        return ObjC.classes.NSBundle.mainBundle().bundleIdentifier().toString();
    }
}

// Is the pointer executable code belonging to the flutter library?
// Deliberately asks the OS about the mapping instead of using PT_LOAD_text_p_vaddr /
// TEXT_segment_text_section_offset: on some libflutter.so builds the first PT_LOAD is the
// R-E segment at vaddr 0 (so parseElf files it as "rodata") and PT_LOAD_text_p_vaddr ends up
// on the RW data segment, and android libraries can have several executable segments.
function isInTextSection(p) {
    if (p == null || flutter_base == null) {
        return false;
    }
    var addr = ptr(p);
    var module = Process.findModuleByAddress(addr);
    if (module === null || module.base.compare(flutter_base) !== 0) {
        return false;
    }
    var range = Process.findRangeByAddress(addr);
    if (range === null) {
        // Cannot tell: being inside the flutter module is good enough to disambiguate
        return true;
    }
    return range.protection.indexOf('x') !== -1;
}

// Convert hex to byte string
function convertHexToByteString(hexString) {
    // Remove the '0x' prefix
    let cleanHexString = hexString.startsWith('0x') ? hexString.slice(2) : hexString;

    // Pad with a leading zero if the length is odd
    if (cleanHexString.length % 2 !== 0) {
        cleanHexString = '0' + cleanHexString;
    }

    // Split the string into pairs of two characters
    let byteArray = cleanHexString.match(/.{1,2}/g);

    // Reverse the order of the byte pairs
    byteArray.reverse();

    // Join the byte pairs with spaces
    let byteString = byteArray.join(' ');

    return byteString;
}

// Convert ip string (e.g, "192.168.0.12") to byte array
function convertIpToByteArray(ipString) {
    // Split the IP address into its components
    let octets = ipString.split('.');

    // Convert each octet to a hexadecimal number and then to a byte
    let byteArray = octets.map(octet => parseInt(octet, 10));

    return byteArray;
}

// Convert ArrayBuffer to hex string
function convertArrayBufferToHex(buffer) {
    let hexArray = [];
    let uint8Array = new Uint8Array(buffer);
    for (let byte of uint8Array) {
        hexArray.push(byte.toString(16).padStart(2, '0'));
    }
    return hexArray.join(' ');
}

// Byte flip
function byteFlip(number) {
    // Extract the high and low bytes
    let highByte = (number >> 8) & 0xFF;
    let lowByte = number & 0xFF;

    // Swap the high and low bytes
    let flippedNumber = (lowByte << 8) | highByte;

    return flippedNumber;
}

// Memory scan
function scanMemory(scan_start_addr, scan_size, pattern, for_what) {
    Memory.scan(scan_start_addr, scan_size, pattern, {
        onMatch: function(address, size){
            if (for_what == "ssl_client") {
                ssl_client_string_pattern_found_addr = address;
                console.log(`[*] ssl_client string pattern found at: ${address}`);
            }
            else if (for_what == "ssl_client_adrp_add") {
                var adrp, add;
                var disasm = Instruction.parse(address);
                if (disasm.mnemonic == "adrp") {
                    adrp = disasm.operands.find(op => op.type === 'imm')?.value;

                    disasm = Instruction.parse(disasm.next);
                    if (disasm.mnemonic != "add") {
                        disasm = Instruction.parse(disasm.next);
                    }
                    add = disasm.operands.find(op => op.type === 'imm')?.value;

                    if (adrp != undefined && add != undefined && ptr(adrp).add(add).toString() == ssl_client_string_pattern_found_addr.toString()) {
                        console.log(`[*] Found adrp add address: ${address}`);
                        // As we trace back, disassemble to find the address of the verify_cert_chain function (https://blog.weghos.com/flutter/engine/third_party/boringssl/src/ssl/ssl_x509.cc.html#_ZN4bsslL41ssl_crypto_x509_session_verify_cert_chainEP14ssl_session_stPNS_13SSL_HANDSHAKEEPh)
                        // Bounded only to stop an unbounded back-walk hanging the agent; kept wide
                        // because real call sites sit up to ~0x5cc bytes past the prologue.
                        for (let off = 0; off < 0x1000; off += 4) {
                            disasm = Instruction.parse(address.sub(off));
                            if (disasm.mnemonic == "sub") {
                                disasm = Instruction.parse(disasm.next);
                                if (disasm.mnemonic == "stp" || disasm.mnemonic == "str") {
                                    verify_cert_chain_func_addr = address.sub(off);
                                    console.log(`[*] Found verify_cert_chain function address: ${verify_cert_chain_func_addr}`);
                                    break;
                                }
                            } else {
                                continue;
                            }
                        }
                    }
                }
            }
            else if (for_what == "ssl_client_lea_rdi_rip") {
                /* opcode
                    lea rdi, [rip - 0xabcd]
                */
                var rdi, rip, disp;
                var disasm = Instruction.parse(address);
                if (disasm.mnemonic == "lea") {
                    rip = disasm.next;
                    disp = disasm.operands.find(op => op.type === 'mem')?.value.disp;
                    rdi = rip.add(disp);

                    if (rip != undefined && rdi != undefined && ptr(rdi).toString() == ssl_client_string_pattern_found_addr.toString()) {
                        console.log(`[*] Found lea rdi rip address: ${address}`);
                        // As we trace back, disassemble to find the address of the verify_cert_chain function (https://blog.weghos.com/flutter/engine/third_party/boringssl/src/ssl/ssl_x509.cc.html#_ZN4bsslL41ssl_crypto_x509_session_verify_cert_chainEP14ssl_session_stPNS_13SSL_HANDSHAKEEPh)
                        for (let off = 0;; off += 1) {
                            try {
                                disasm = Instruction.parse(address.sub(off));
                                if (disasm.mnemonic == "push" && disasm.opStr == "rbp") {
                                    if (Instruction.parse(disasm.next) != 'push r15') {
                                        continue;
                                    }
                                    verify_cert_chain_func_addr = address.sub(off);
                                    console.log(`[*] Found verify_cert_chain function address: ${verify_cert_chain_func_addr}`);
                                    break;
                                } else {
                                    continue;
                                }
                            } catch (error) {
                                continue;
                            }
                        }
                    }
                }
            }
            else if (for_what == "handshake") {
                // adrp/add materialises the address of the whole C string, so walk back to the start of
                // the string (the NUL terminating the previous one) instead of looking for a literal
                // "../../": this build's path is "../../../flutter/third_party/..." and matching "../../"
                // stopped 3 bytes into it, so the address comparison below could never succeed.
                handshake_string_pattern_found_addr = null;
                var max_string_walk = 0x200;
                for (let off = 1; off <= max_string_walk; off += 1) {
                    if (ptr(address).sub(off).readU8() == 0x00) {
                        handshake_string_pattern_found_addr = ptr(address).sub(off - 1);
                        break;
                    }
                }
                if (handshake_string_pattern_found_addr == null) {
                    console.log("[!] Could not find the start of the handshake.cc string");
                    return;
                }
                console.log(`[*] handshake string pattern found at: ${handshake_string_pattern_found_addr}`);
                // Get the iOS app id. if it's too early app crashes when spawning the iOS flutter app. this location is safe.
                appId_iOS = findAppId();
            }
            else if (for_what == "handshake_adrp_add") {
                var adrp, add;
                var disasm = Instruction.parse(address);
                if (disasm.mnemonic == "adrp") {
                    adrp = disasm.operands.find(op => op.type === 'imm')?.value;

                    disasm = Instruction.parse(disasm.next);
                    if (disasm.mnemonic != "add") {
                        disasm = Instruction.parse(disasm.next);
                    }
                    add = disasm.operands.find(op => op.type === 'imm')?.value;

                    if (adrp != undefined && add != undefined && ptr(adrp).add(add).toString() == handshake_string_pattern_found_addr.toString()) {
                        console.log(`[*] Found adrp add address: ${address}`);
                        // As we trace back, disassemble to find the address of the ssl_verify_peer_cert function (https://blog.weghos.com/flutter/engine/third_party/boringssl/src/ssl/handshake.cc.html#_ZN4bssl20ssl_verify_peer_certEPNS_13SSL_HANDSHAKEE)
                        // Bounded only to stop an unbounded back-walk hanging the agent; kept wide
                        // because real call sites sit up to ~0x5cc bytes past the prologue.
                        for (let off = 0; off < 0x1000; off += 4) {
                            disasm = Instruction.parse(address.sub(off));
                            if (disasm.mnemonic == "sub") {
                                disasm = Instruction.parse(disasm.next);
                                if (disasm.mnemonic == "stp" || disasm.mnemonic == "str") {
                                    verify_peer_cert_func_addr = address.sub(off);
                                    console.log(`[*] Found verify_peer_cert function address: ${verify_peer_cert_func_addr}`);
                                    break;
                                }
                            } else {
                                continue;
                            }
                        }
                    }
                }
            }
            else if (for_what == "Socket_CreateConnect") {
                Socket_CreateConnect_string_pattern_found_addr = address;
                console.log(`[*] Socket_CreateConnect string pattern found at: ${address}`);
            }
            else if (for_what == "Socket_CreateConnect_func_addr") {
                // The Dart native entry is a 3-field struct {name, function, argument_count}, but the
                // field order varies between engine builds. Disambiguate with the argument_count field:
                // it is the only one holding a small integer, so it tells us which layout we are on.
                //   {name, func, argc}: argc at name+0x10, func at name+0x8   (current iOS builds)
                //   {func, argc, name}: argc at name-0x08, func at name-0x10
                Socket_CreateConnect_func_addr = null;
                var entry_layouts = [
                    { argc_offset: 0x10, func_offset: 0x8 },
                    { argc_offset: -0x8, func_offset: -0x10 },
                ];
                for (var l = 0; l < entry_layouts.length; l++) {
                    try {
                        var argc = address.add(entry_layouts[l].argc_offset).readU64().toNumber();
                        var candidate = address.add(entry_layouts[l].func_offset).readPointer();
                        if (argc > 0 && argc < 0x100 && isInTextSection(candidate)) {
                            Socket_CreateConnect_func_addr = candidate;
                            console.log(`[*] Native entry layout: function at name+0x${entry_layouts[l].func_offset.toString(16)}, argument_count ${argc}`);
                            break;
                        }
                    } catch (error) {
                        continue;
                    }
                }
                if (Socket_CreateConnect_func_addr == null) {
                    console.log("[!] Could not resolve the function pointer of the Socket_CreateConnect native entry, skipping this match");
                    return;
                }
                console.log(`[*] Found Socket_CreateConnect function address: ${Socket_CreateConnect_func_addr}`);
                /* arm64
                    Socket_CreateConnect function looks like this.
                    SUB             SP, SP, #0xD0
                    STR             X30, [SP,#0xD0+var_30]
                    STP             X22, X21, [SP,#0xD0+var_20]
                    STP             X20, X19, [SP,#0xD0+var_10]
                    MOV             W1, #1
                    MOV             X19, X0
                    BL              sub_89E20C
                    ADD             X1, SP, #0xD0+var_B0
                    BL              loc_67C15C   <---------------- branch to GetSockAddr function
                    MOV             W1, #2
                    MOV             X0, X19
                    BL              sub_89E20C
                */

                /* x64
                    push            rbp
                    push            r15
                    push            r14
                    push            r13
                    push            r12
                    push            rbx
                    sub             rsp, 498h
                    mov             rbx, rdi
                    mov             esi, 1
                    call            sub_AB2790
                    lea             rsi, [rsp+4C8h+addr]
                    mov             rdi, rax
                    call            sub_8EEB50  <---------------- branch to GetSockAddr function
                    mov             rdi, rbx
                    mov             esi, 2
                    call            sub_AB2790
                */

                if (Process.arch == 'arm64') {
                    var bl_count = 0;
                    // Bounded: an unbounded walk runs off the end of the function and hangs the
                    // agent when the expected two bl instructions are not there.
                    var max_scan_bytes = 0x200;
                    for (let off = 0; off < max_scan_bytes; off += 4) {
                        let disasm = Instruction.parse(Socket_CreateConnect_func_addr.add(off));
                        if (disasm.mnemonic == "bl") {
                            bl_count++;
                            if (bl_count == 2) {
                                GetSockAddr_func_addr = ptr(disasm.operands.find(op => op.type === 'imm')?.value);
                                console.log(`[*] Found GetSockAddr function address: ${GetSockAddr_func_addr}`);
                                break;
                            } else {
                                continue;
                            }
                        }
                    }
                } else if (Process.arch == 'x64') {
                    var call_count = 0;
                    var max_scan_bytes = 0x300;
                    for (let off = 0; off < max_scan_bytes; off += 1)
                    {
                        try {
                            let disasm = Instruction.parse(Socket_CreateConnect_func_addr.add(off));
                            if (disasm.mnemonic == "call") {
                                call_count++;
                                if (call_count == 2) {
                                    GetSockAddr_func_addr = ptr(disasm.operands.find(op => op.type === 'imm')?.value);
                                    console.log(`[*] Found GetSockAddr function address: ${GetSockAddr_func_addr}`);
                                    break;
                                } else {
                                    continue;
                                }
                            }
                        } catch (error) {
                            continue;
                        }
                    }
                }
                if (GetSockAddr_func_addr == null) {
                    console.log("[!] Could not find the GetSockAddr branch inside Socket_CreateConnect");
                }
            }
        },
        onComplete: function(){
            // Scan adrp add opcode on the .text section to find the function which has "ssl_client" string
            if (for_what == "ssl_client" && ssl_client_string_pattern_found_addr != null) {
                if (Process.arch == 'arm64') {
                    var adrp_add_pattern = "?9 ?? ?? ?0 29 ?? ?? 91";
                    if (appId == "com.alibaba.intl.android.apps.poseidon") {
                        // alibaba.com (android) adrp add pattern is different
                        adrp_add_pattern = "?9 ?? ?? ?0 ?? ?? ?? ?? 29 ?? ?? 91";
                    }
                    scanMemory(flutter_base.add(PT_LOAD_text_p_vaddr), PT_LOAD_text_p_memsz, adrp_add_pattern, "ssl_client_adrp_add");
                } else if (Process.arch == 'x64') {
                    var lea_rdi_rip_pattern = "48 8d 3d ?? ?? ?? FF";
                    scanMemory(flutter_base.add(PT_LOAD_text_p_vaddr), PT_LOAD_text_p_memsz, lea_rdi_rip_pattern, "ssl_client_lea_rdi_rip");
                }
            }
            else if (for_what == "handshake" && handshake_string_pattern_found_addr != null) {
                // The last instruction of the pattern is "mov w3, #<line>", the handshake.cc source line
                // number of the OPENSSL_PUT_ERROR call. It moves with every boringssl update, which made
                // this scan return nothing. Wildcard the immediate but keep the movz-into-w3 shape;
                // "mov w1, #0x111" (SSL_R_CERTIFICATE_VERIFY_FAILED) still pins it to a single site.
                var adrp_add_pattern = "?2 ?? 00 ?0 42 ?? ?? 91 00 02 80 52 21 22 80 52 ?3 ?? 80 52";
                // In case we don't get the iOS app id yet, try to get it again after 0.1 second. This happens when spawning the iOS Flutter app
                if (appId_iOS == null) {
                    Thread.sleep(0.1);
                    appId_iOS = findAppId();
                }
                if (appId_iOS == "com.alibaba.sourcing") {
                    // alibaba.com (iOS) adrp add pattern is different
                    adrp_add_pattern = "?3 ?? 00 ?0 63 ?? ?? 91 00 02 80 52 01 00 80 52 22 22 80 52 84 25 80 52"
                }
                scanMemory(flutter_base.add(TEXT_segment_text_section_offset), TEXT_segment_text_section_size, adrp_add_pattern, "handshake_adrp_add");
            }
            // Scan "Socket_CreateConnect" string pattern found address on the .data.rel.ro section to find the address of "Socket_CreateConnect" function
            else if (for_what == "Socket_CreateConnect" && Socket_CreateConnect_string_pattern_found_addr != null) {
                var addr_to_find = convertHexToByteString(Socket_CreateConnect_string_pattern_found_addr.toString());
                if (Process.platform === 'linux') {
                    scanMemory(flutter_base.add(PT_GNU_RELRO_p_vaddr), PT_GNU_RELRO_p_memsz, addr_to_find, "Socket_CreateConnect_func_addr");
                }
                else if (Process.platform === 'darwin') {
                    if (DATA_segment_const_section_offset === null || DATA_segment_const_section_size === null) {
                        console.log("[!] const section not parsed, cannot scan for the Socket_CreateConnect function address");
                    } else {
                        scanMemory(flutter_base.add(DATA_segment_const_section_offset), DATA_segment_const_section_size, addr_to_find, "Socket_CreateConnect_func_addr");
                    }
                }
            }
            console.log("[*] scan memory done");
        }
    })
}
/* Util functions */

/* Some variables and functions for elf parsing */
var O_RDONLY = 0;
var O_WRONLY = 1;
var O_RDWR = 2;
var O_APPEND = 1024;
var O_LARGEFILE = 32768;
var O_CREAT = 64;
var SEEK_SET = 0;
var SEEK_CUR = 1;
var SEEK_END = 2;

var p_types = {
    "PT_NULL":		0,		/* Program header table entry unused */
    "PT_LOAD":		1,		/* Loadable program segment */
    "PT_DYNAMIC":	2,		/* Dynamic linking information */
    "PT_INTERP":	3,		/* Program interpreter */
    "PT_NOTE":		4,		/* Auxiliary information */
    "PT_SHLIB":	    5,		/* Reserved */
    "PT_PHDR":		6,		/* Entry for header table itself */
    "PT_TLS":		7,		/* Thread-local storage segment */
    "PT_NUM":		8,		/* Number of defined types */
    "PT_LOOS":		0x60000000,	/* Start of OS-specific */
    "PT_GNU_EH_FRAME":	0x6474e550,	/* GCC .eh_frame_hdr segment */
    "PT_GNU_STACK":	0x6474e551,	/* Indicates stack executability */
    "PT_GNU_RELRO":	0x6474e552,	/* Read-only after relocation */
    "PT_GNU_PROPERTY":	0x6474e553,	/* GNU property */
    "PT_LOSUNW":	0x6ffffffa,
    "PT_SUNWBSS":	0x6ffffffa,	/* Sun Specific segment */
    "PT_SUNWSTACK":	0x6ffffffb,	/* Stack segment */
    "PT_HISUNW":	0x6fffffff,
    "PT_HIOS":		0x6fffffff,	/* End of OS-specific */
    "PT_LOPROC":	0x70000000,	/* Start of processor-specific */
    "PT_HIPROC":	0x7fffffff,	/* End of processor-specific */
}

function getExportFunction(name, ret, args) {
    var funcPtr;
    funcPtr = Module.findExportByName(null, name);
    if (funcPtr === null) {
        console.log("cannot find " + name);
        return null;
    } else {
        var func = new NativeFunction(funcPtr, ret, args);
        if (typeof func === "undefined") {
            console.log("parse error " + name);
            return null;
        }
        return func;
    }
}

var open = getExportFunction("open", "int", ["pointer", "int", "int"])
var close = getExportFunction("close", "int", ["int"]);
var lseek = getExportFunction("lseek", "int", ["int", "int", "int"]);
var read = getExportFunction("read", "int", ["int", "pointer", "int"]);
/* Some variables and functions for elf parsing */

/* Parsing elf function */
function parseElf(base) {
    base = ptr(base);
    var module = Process.findModuleByAddress(base);
    var fd = null;
    if (module !== null) {
        fd = open(Memory.allocUtf8String(module.path), O_RDONLY, 0);
    }

    // Read elf header
    var magic = "464c457f"
    var elf_magic = base.readU32()
    if (parseInt(elf_magic).toString(16) != magic) {
        console.log("[!] Wrong magic...ignore")
    }

    var arch = Process.arch
    var is32bit = arch == "arm" ? 1 : 0 // 1:32 0:64

    var size_of_Elf32_Ehdr = 0x34;
    var off_of_Elf32_Ehdr_shoff = 32;
    var off_of_Elf32_Ehdr_phentsize = 42;
    var off_of_Elf32_Ehdr_phnum = 44;
    var off_of_Elf32_Ehdr_shentsize = 46;
    var off_of_Elf32_Ehdr_shnum = 48;
    var off_of_Elf32_Ehdr_shstrndx = 50;

    var size_of_Elf64_Ehdr = 0x40;
    var off_of_Elf64_Ehdr_shoff = 40;
    var off_of_Elf64_Ehdr_phentsize = 54;
    var off_of_Elf64_Ehdr_phnum = 56;
    var off_of_Elf64_Ehdr_shentsize = 58;
    var off_of_Elf64_Ehdr_shnum = 60;
    var off_of_Elf64_Ehdr_shstrndx = 62;

    // Parse Ehdr(Elf header)
    var ehdrs_from_file = null;
    var phoff = is32bit ? size_of_Elf32_Ehdr : size_of_Elf64_Ehdr   // Program header table file offset
    var shoff = is32bit ? base.add(off_of_Elf32_Ehdr_shoff).readU32() : base.add(off_of_Elf64_Ehdr_shoff).readU64();   // Section header table file offset
    if (shoff == 0 && fd != null && fd !== -1) {
        console.log("[!] shoff is 0. Try to get it from the file")
        ehdrs_from_file = Memory.alloc(64);
        lseek(fd, 0, SEEK_SET);
        read(fd, ehdrs_from_file, 64);
        shoff = is32bit ? ehdrs_from_file.add(off_of_Elf32_Ehdr_shoff).readU32() : ehdrs_from_file.add(off_of_Elf64_Ehdr_shoff).readU64();
        console.log(`[*] shoff from the file: ${shoff}`)
    }
    var phentsize = is32bit ? base.add(off_of_Elf32_Ehdr_phentsize).readU16() : base.add(off_of_Elf64_Ehdr_phentsize).readU16();    // Size of entries in the program header table
    if (is32bit && phentsize != 32) {  // 0x20
        console.log("[!] Wrong e_phentsize. Should be 32. Let's assume it's 32");
        phentsize = 32;
    } else if (!is32bit && phentsize != 56) {
        console.log("[!] Wrong e_phentsize. Should be 56. Let's assume it's 56");
        phentsize = 56;
    }
    var phnum = is32bit ? base.add(off_of_Elf32_Ehdr_phnum).readU16() : base.add(off_of_Elf64_Ehdr_phnum).readU16();    // Number of entries in program header table
    // If phnum is 0, try to get it from the file
    if (phnum == 0) {
        if (fd != null && fd !== -1){
            console.log("[!] phnum is 0. Try to get it from the file")
            ehdrs_from_file = Memory.alloc(64);
            lseek(fd, 0, SEEK_SET);
            read(fd, ehdrs_from_file, 64);
            phnum = is32bit ? ehdrs_from_file.add(off_of_Elf32_Ehdr_phnum).readU16() : ehdrs_from_file.add(off_of_Elf64_Ehdr_phnum).readU16();
            if (phnum == 0) {
                console.log("[!] phnum is still 0. Let's assume it's 10. because we just need to find .dynamic section");
                phnum = 10;
            } else {
                console.log(`[*] phnum from the file: ${phnum}`)
            }
        } else {
            console.log("[!] phnum is 0. Let's assume it's 10. because we just need to find .dynamic section")
            phnum = 10;
        }
    }

    var shentsize = is32bit ? base.add(off_of_Elf32_Ehdr_shentsize).readU16() : base.add(off_of_Elf64_Ehdr_shentsize).readU16();    // Size of the section header
    if (is32bit && shentsize != 40) {  // 0x28
        console.log("[!] Wrong e_shentsize. Let's assume it's 40");
        shentsize = 40;
    } else if (!is32bit && shentsize != 64) {
        console.log("[!] Wrong e_shentsize. Let's assume it's 64");
        shentsize = 64;
    }
    var shnum = is32bit ? base.add(off_of_Elf32_Ehdr_shnum).readU16() : base.add(off_of_Elf64_Ehdr_shnum).readU16();    // Number of entries in section header table
    var shstrndx = is32bit ? base.add(off_of_Elf32_Ehdr_shstrndx).readU16() : base.add(off_of_Elf64_Ehdr_shstrndx).readU16();  // Section header table index of the entry associated with the section name string table
    if (shnum == 0 && fd != null && fd !== -1) {
        console.log("[!] shnum is 0. Try to get it from the file");
        ehdrs_from_file = Memory.alloc(64);
        lseek(fd, 0, SEEK_SET);
        read(fd, ehdrs_from_file, 64);
        shnum = is32bit ? ehdrs_from_file.add(off_of_Elf32_Ehdr_shnum).readU16() : ehdrs_from_file.add(off_of_Elf64_Ehdr_shnum).readU16();
        shstrndx = is32bit ? ehdrs_from_file.add(off_of_Elf32_Ehdr_shstrndx).readU16() : ehdrs_from_file.add(off_of_Elf64_Ehdr_shstrndx).readU16();
        console.log(`[*] shnum from the file: ${shnum}, shstrndx from the file: ${shstrndx}`)
    }
    // console.log(`phoff: ${phoff}, shoff: ${shoff}, phentsize: ${phentsize}, phnum: ${phnum}, shentsize: ${shentsize}, shnum: ${shnum}, shstrndx: ${shstrndx}`)

    // Parse Phdr(Program header)
    var phdrs = base.add(phoff)
    for (var i = 0; i < phnum; i++) {
        var phdr = phdrs.add(i * phentsize);
        var p_type = phdr.readU32();

        // if p_type is 0 check if it's really 0 from the file
        var phdrs_from_file = null;
        if (p_type === 0 && fd != null && fd !== -1) {
            phdrs_from_file = Memory.alloc(phnum * phentsize);
            lseek(fd, phoff, SEEK_SET);
            read(fd, phdrs_from_file, phnum * phentsize);
            p_type = phdrs_from_file.add(i * phentsize).readU32();
        }
        var p_type_sym = null;

        // check if p_type matches the defined p_type
        var p_type_exists = false;
        for (let key in p_types) {
            if (p_types[key] === p_type) {
                p_type_exists = true;
                p_type_sym = key;
                break;
            }
        }
        if (!p_type_exists) break;

        var p_offset = is32bit ? phdr.add(0x4).readU32() : phdr.add(0x8).readU64();
        var p_vaddr = is32bit ? phdr.add(0x8).readU32() : phdr.add(0x10).readU64();
        var p_paddr = is32bit ? phdr.add(0xc).readU32() : phdr.add(0x18).readU64();
        var p_filesz = is32bit ? phdr.add(0x10).readU32() : phdr.add(0x20).readU64();
        var p_memsz = is32bit ? phdr.add(0x14).readU32() : phdr.add(0x28).readU64();
        var p_flags = is32bit ? phdr.add(0x18).readU32() : phdr.add(0x4).readU32();
        var p_align = is32bit ? phdr.add(0x1c).readU32() : phdr.add(0x30).readU64();
        // console.log(`p_type: ${p_type}, p_offset: ${p_offset}, p_vaddr: ${p_vaddr}, p_paddr: ${p_paddr}, p_filesz: ${p_filesz}, p_memsz: ${p_memsz}, p_flags: ${p_flags}, p_align: {p_align}`);

        // if p_flags is 0, check it from the file
        if (p_flags === 0 && fd != null && fd !== -1) {
            phdrs_from_file = Memory.alloc(phnum * phentsize);
            lseek(fd, phoff, SEEK_SET);
            read(fd, phdrs_from_file, phnum * phentsize);
            var phdr_from_file = phdrs_from_file.add(i * phentsize);
            p_offset = is32bit ? phdr_from_file.add(0x4).readU32() : phdr_from_file.add(0x8).readU64();
            p_vaddr = is32bit ? phdr_from_file.add(0x8).readU32() : phdr_from_file.add(0x10).readU64();
            p_paddr = is32bit ? phdr_from_file.add(0xc).readU32() : phdr_from_file.add(0x18).readU64();
            p_filesz = is32bit ? phdr_from_file.add(0x10).readU32() : phdr_from_file.add(0x20).readU64();
            p_memsz = is32bit ? phdr_from_file.add(0x14).readU32() : phdr_from_file.add(0x28).readU64();
            p_flags = is32bit ? phdr_from_file.add(0x18).readU32() : phdr_from_file.add(0x4).readU32();
            p_align = is32bit ? phdr_from_file.add(0x1c).readU32() : phdr_from_file.add(0x30).readU64();
        }

        // .rodata section
        if (p_type_sym === 'PT_LOAD' && p_vaddr == 0) {
            PT_LOAD_rodata_p_memsz = p_memsz;
            continue;
        }

        // .text section
        if (p_type_sym === 'PT_LOAD' && p_vaddr != 0) {
            if (PT_LOAD_text_p_vaddr == null && PT_LOAD_text_p_memsz == null) {
                PT_LOAD_text_p_vaddr = p_vaddr;
                PT_LOAD_text_p_memsz = p_memsz;
            }
            continue;
        }

        if (p_type_sym === 'PT_GNU_RELRO') {
            PT_GNU_RELRO_p_vaddr = p_vaddr;
            PT_GNU_RELRO_p_memsz = p_memsz;
            break;
        }
    }
}
/* Parsing elf function */

/* Parsing MachO function */
function parseMachO(base) {
    base = ptr(base);
    var magic = base.readU32();
    if (magic != 0xfeedfacf) {
        console.log('[!] Unknown or unsupported magic: 0x' + magic.toString(16) + ' (only 64-bit MachO is supported)');
        return;
    }

    var LC_SEGMENT_64 = 0x19;
    var number_of_commands_offset = 0x10;
    var load_command_size_offset = 0x4;
    var segment_name_offset = 0x8;
    var vm_address_offset = 0x18;
    var number_of_sections_offset = 0x40;
    var section64_header_base_offset = 0x48;
    var section64_header_size = 0x50;
    // struct section_64: sectname[16], segname[16], addr(u64)@0x20, size(u64)@0x28, offset(u32)@0x30
    var section_addr_offset = 0x20;
    var section_size_offset = 0x28;

    var cmdnum = base.add(number_of_commands_offset).readU32();
    var cmdoff = 0x20;
    var text_segment_vmaddr = null;
    // Collect every section first, then pick the ones we need. Section names alone are ambiguous
    // (e.g. both __TEXT and __DATA_CONST have a __const), so key on "segment,section".
    var sections = {};

    for (var cmd_index = 0; cmd_index < cmdnum; cmd_index++) {
        var cmd = base.add(cmdoff).readU32();
        var cmdsize = base.add(cmdoff + load_command_size_offset).readU32();
        if (cmdsize == 0) {
            break;
        }
        if (cmd === LC_SEGMENT_64) {
            var segname = base.add(cmdoff + segment_name_offset).readUtf8String();
            var vmaddr = base.add(cmdoff + vm_address_offset).readU64().toNumber();
            var nsects = base.add(cmdoff + number_of_sections_offset).readU32();
            var secbase = base.add(cmdoff + section64_header_base_offset);

            // flutter_base is where __TEXT got mapped, so every offset we hand out is relative to it
            if (segname === '__TEXT' && text_segment_vmaddr === null) {
                text_segment_vmaddr = vmaddr;
            }

            if (text_segment_vmaddr !== null && cmdsize >= section64_header_base_offset + nsects * section64_header_size) {
                // Use a loop variable of its own: reusing the outer `i` used to clobber the
                // load command counter and cut the command walk short.
                for (var sect_index = 0; sect_index < nsects; sect_index++) {
                    var sechdr = secbase.add(sect_index * section64_header_size);
                    var secname = sechdr.readUtf8String();
                    // Derive the offset from the section vmaddr instead of its file offset:
                    // zero-fill sections (__bss, __common) have no file offset at all.
                    var section_offset = sechdr.add(section_addr_offset).readU64().toNumber() - text_segment_vmaddr;
                    // Take the size straight from the section header rather than diffing against the
                    // next section, which broke whenever the section we want is the last of its segment.
                    var section_size = sechdr.add(section_size_offset).readU64().toNumber();
                    sections[segname + ',' + secname] = { offset: section_offset, size: section_size };
                }
            }
        }
        cmdoff += cmdsize;
    }

    function pickSection(candidates) {
        for (var n = 0; n < candidates.length; n++) {
            if (sections[candidates[n]] !== undefined) {
                return { key: candidates[n], value: sections[candidates[n]] };
            }
        }
        return null;
    }

    var text_section = pickSection(['__TEXT,__text']);
    if (text_section !== null) {
        TEXT_segment_text_section_offset = text_section.value.offset;
        TEXT_segment_text_section_size = text_section.value.size;
    }

    var cstring_section = pickSection(['__TEXT,__cstring']);
    if (cstring_section !== null) {
        TEXT_segment_cstring_section_offset = cstring_section.value.offset;
        TEXT_segment_cstring_section_size = cstring_section.value.size;
    }

    // Current iOS toolchains move the read-only pointer tables (where the Socket_CreateConnect
    // native entry lives) into __DATA_CONST,__const. Older builds keep them in __DATA,__const.
    var const_section = pickSection(['__DATA_CONST,__const', '__DATA,__const']);
    if (const_section !== null) {
        DATA_segment_const_section_offset = const_section.value.offset;
        DATA_segment_const_section_size = const_section.value.size;
        console.log(`[*] Using ${const_section.key} for the const pointer table: base+0x${DATA_segment_const_section_offset.toString(16)} size 0x${DATA_segment_const_section_size.toString(16)}`);
    } else {
        console.log('[!] Could not locate a __const section in __DATA_CONST or __DATA');
    }
}
/* Parsing MachO function */

/* Hook flutter engine function to capture the network traffic */
function hook(target) {
    if (target == "GetSockAddr") {
        // Hook SocketAddress::GetSockAddr function so we can get the address of sockaddr structure
        Interceptor.attach(GetSockAddr_func_addr, {
            onEnter: function(args) {
                // console.log(`[!] sockaddr: ${args[1]}`);
                sockaddr = args[1];
            },
            onLeave: function(retval) {}
        })
        // Hook the socket function and replace the IP and port with our burp ones.
        Interceptor.attach(Module.findExportByName(null, "socket"), {
            onEnter: function(args) {
                // AF_INET(IPv4) == 2, AF_INET6(IPv6) == 10
                var overwrite = false;
                if (Process.platform === 'linux' && sockaddr != null && ptr(sockaddr).readU16() == 2) {
                    overwrite = true;
                }
                else if (Process.platform === 'darwin' && sockaddr != null && ptr(sockaddr).add(0x1).readU8() == 2) {
                    overwrite = true;
                }

                if (overwrite) {
                    console.log(`[*] Overwrite sockaddr as our burp proxy ip and port --> ${BURP_PROXY_IP}:${BURP_PROXY_PORT}`);
                    ptr(sockaddr).add(0x2).writeU16(byteFlip(BURP_PROXY_PORT));
                    ptr(sockaddr).add(0x4).writeByteArray(convertIpToByteArray(BURP_PROXY_IP));
                }
            },
            onLeave: function(retval) {}
        })
    }
    else if (target == "verifyCertChain") {
        // Hook the verify_cert_chain function and replace the return value with true, so we can capture ssl traffic
        Interceptor.attach(verify_cert_chain_func_addr, {
            onEnter: function(args) {},
            onLeave: function(retval) {
                if (retval == "0x0") {
                    console.log(`[*] verify cert bypass`);
                    var newretval = ptr(0x1);
                    retval.replace(newretval);
                }
            }
        })
    }
    else if (target == "verifyPeerCert") {
        // Hook the verify_peer_cert function and replace it, so we can capture ssl traffic
        // https://github.com/NVISOsecurity/disable-flutter-tls-verification/blob/ecc6e9ed9e1182645b32da68d7be6aefb2b7e970/disable-flutter-tls.js#L151
        Interceptor.replace(verify_peer_cert_func_addr, new NativeCallback((pathPtr, flags) => {
            console.log(`[*] verify peer cert bypass`);
            return 0;
        }, 'int', ['pointer', 'int']));
    }
}
/* Hook flutter engine function to capture the network traffic */

/* main */
var target_flutter_library = ObjC.available ? "Flutter.framework/Flutter" : (Java.available ? "libflutter.so" : null);
if (target_flutter_library != null) {
    var awaitForCondition = function(callback) {
        var module_loaded = 0;
        var base = null;
        var int = setInterval(function() {
            Process.enumerateModules()
            .filter(function(m){ return m['path'].indexOf(target_flutter_library) != -1; })
            .forEach(function(m) {
                if (ObjC.available) {
                    target_flutter_library = target_flutter_library.split('/').pop();
                }
                console.log(`[*] ${target_flutter_library} loaded!`);
                base = Process.getModuleByName(target_flutter_library).base;
                return module_loaded = 1;
            })
            if(module_loaded) {
                clearInterval(int);
                callback(+base);
                return;
            }
        }, 0);
    }

    function init(base) {
        flutter_base = ptr(base);
        console.log(`[*] ${target_flutter_library} base: ${flutter_base}`);
        if (Process.platform === 'linux') {
            appId = findAppId();
            console.log(`[*] package name: ${appId}`);
        }

        var ssl_client_string = '73 73 6C 5F 63 6C 69 65 6E 74 00';
        var Socket_CreateConnect_string = '53 6f 63 6b 65 74 5f 43 72 65 61 74 65 43 6f 6e 6e 65 63 74 00';
        // "third_party/boringssl/src/ssl/handshake.cc" string. First, Scan this string and then need to find the start address of "../../"
        var handshake_string = '74 68 69 72 64 5f 70 61 72 74 79 2f 62 6f 72 69 6e 67 73 73 6c 2f 73 72 63 2f 73 73 6c 2f 68 61 6e 64 73 68 61 6b 65 2e 63 63';
        if (Process.platform === 'linux') {
            parseElf(flutter_base);
            if (PT_LOAD_rodata_p_memsz != null) {
                // "ssl_client" string scan from the libflutter base address to the right before the .text section
                scanMemory(flutter_base, PT_LOAD_rodata_p_memsz, ssl_client_string, "ssl_client");
                // "Socket_CreateConnect" string scan
                scanMemory(flutter_base, PT_LOAD_rodata_p_memsz, Socket_CreateConnect_string, "Socket_CreateConnect");
            }
        }
        else if (Process.platform === 'darwin') {
            parseMachO(flutter_base);
            // Find verify_peer_cert function address by scanning "third_party/boringssl/src/ssl/handshake.cc" string
            if (TEXT_segment_cstring_section_offset === null || TEXT_segment_cstring_section_size === null) {
                console.log("[!] __TEXT,__cstring not parsed, aborting the string scans");
                return;
            }
            scanMemory(flutter_base.add(TEXT_segment_cstring_section_offset), TEXT_segment_cstring_section_size, handshake_string, "handshake");
            scanMemory(flutter_base.add(TEXT_segment_cstring_section_offset), TEXT_segment_cstring_section_size, Socket_CreateConnect_string, "Socket_CreateConnect");
        }

        var int_getSockAddr = setInterval(() => {
            if (GetSockAddr_func_addr != null) {
                console.log("[*] Hook GetSockAddr function");
                hook("GetSockAddr");
                clearInterval(int_getSockAddr);
            }
        }, 0);

        if (Process.platform === 'linux') {
            var int_verifyCertBypass = setInterval(() => {
                if (verify_cert_chain_func_addr != null) {
                    console.log("[*] Hook verify_cert_chain function");
                    hook("verifyCertChain");
                    clearInterval(int_verifyCertBypass);
                }
            }, 0);
        }
        // On iOS, hooking verify_cert_chain doesn't work. Instead, hook verify_peer_cert
        else if (Process.platform === 'darwin') {
            var int_verifyPeerCertBypass = setInterval(() => {
                if (verify_peer_cert_func_addr != null) {
                    console.log("[*] Hook verify_peer_cert function");
                    hook("verifyPeerCert");
                    clearInterval(int_verifyPeerCertBypass);
                }
            }, 0);
        }
    }

    awaitForCondition(init);
}
/* main */

/* ---- DNS fix: resolve internal .loc names that do not exist in public DNS ----
 * Dart calls getaddrinfo BEFORE connect; if it returns NXDOMAIN it throws
 * "Failed host lookup" and never reaches the GetSockAddr hook. We rewrite the
 * hostname to a resolvable IP so getaddrinfo succeeds; GetSockAddr then
 * redirects the socket to Burp anyway.
 */
(function () {
    var FAKE_IP = BURP_PROXY_IP; // any resolvable IP works; GetSockAddr rewrites the destination regardless
    var keepAlive = [];          // prevents the GC from freeing the strings during the call
    ["getaddrinfo", "android_getaddrinfofornet"].forEach(function (name) {
        var p = Module.findExportByName(null, name) || Module.findExportByName("libc.so", name);
        if (!p) { return; }
        try {
            Interceptor.attach(p, {
                onEnter: function (args) {
                    try {
                        var node = args[0];
                        if (node.isNull()) { return; }
                        var host = node.readCString();
                        if (host && /\.loc$/i.test(host)) {
                            console.log("[DNS] " + name + " " + host + " -> " + FAKE_IP);
                            var repl = Memory.allocUtf8String(FAKE_IP);
                            keepAlive.push(repl);
                            args[0] = repl;
                        }
                    } catch (e) {}
                }
            });
            console.log("[*] Hooked " + name + " to resolve .loc hosts");
        } catch (e) { console.log("[!] Could not hook " + name + ": " + e); }
    });
})();
