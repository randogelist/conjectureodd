/* Native Windows incremental runner. ES3-compatible JScript; no downloaded runtime. */
(function () {
  "use strict";
  var DEFAULT_CONFIG = {
    version: "v0_5_0",
    packageName: "GPKQBKQRXYTENSORHOPF_ODD_ZETA_SHARED_SEQUENCE_LEAN_v0_5_0_construction",
    hashSourceHash: "a8c29c6699432a75ea03541b021e6e722b5d2e0f03dc161241850ad71902c31b",
    planHash: "0150b0eaf9b3a219d5beefc234d4001238f60e56aeccf15fb14b8de9a906a003",
    migrationHash: "bb2277289ccc037e11f12e79602764def818a6d8cdccbc6e74f0c56e2f1eb24c",
    schema: "ZH_NATIVE_RECEIPT_V1",
    auditModule: "ZHPreprint.SharedSequenceAudit",
    auditMarker: "AXIOM_AUDIT_ACCEPTED=ZH_SHARED_SEQUENCE_CLOSURE"
  };
  function fail(s) { throw new Error(s); }
  function has(o, k) { return Object.prototype.hasOwnProperty.call(o, k); }
  function trim(s) { return s.replace(/^\s+|\s+$/g, ""); }
  function lines(s) { return s.replace(/\r/g, "").split("\n"); }
  function isHash(s) { return /^[0-9a-f]{64}$/.test(s); }
  function parseBatchHashes(text, count) {
    var a=lines(text),out=[],i,p;
    if(a.length && a[a.length-1]==="") a.pop();
    if(a.length!==count) fail("BATCH_HASH_ROW_COUNT_MISMATCH");
    for(i=0;i<a.length;i++) {
      p=a[i].split("\t");
      if(p.length!==2 || p[0]!==String(i) || !isHash(p[1])) fail("BATCH_HASH_INVALID_ROW="+i);
      out.push(p[1]);
    }
    return out;
  }
  function moduleOK(s) { return /^[A-Za-z_][A-Za-z0-9_]*(\.[A-Za-z_][A-Za-z0-9_]*)*$/.test(s); }
  function sortedKeys(o) { var a = [], k; for (k in o) if (has(o, k)) a.push(k); return a.sort(); }
  function parsePlan(text) {
    var a = lines(text), out = [], seen = {}, i, p;
    for (i = 0; i < a.length; i++) {
      if (!trim(a[i]) || /^#/.test(a[i])) continue;
      p = a[i].split("\t");
      if (p.length !== 3 || !moduleOK(p[0]) || !isHash(p[2]) ||
          p[1] !== "src/" + p[0].replace(/\./g, "/") + ".lean" || has(seen, p[0]))
        fail("MALFORMED_SOURCE_PLAN");
      seen[p[0]] = true;
      out.push({name:p[0], rel:p[1], sha:p[2]});
    }
    if (!out.length) fail("EMPTY_SOURCE_PLAN");
    return out;
  }
  function parseBaseline(text) {
    var a = lines(text), out = {}, i, p;
    for (i = 0; i < a.length; i++) {
      if (!trim(a[i]) || /^#/.test(a[i])) continue;
      p = a[i].split("\t");
      if (p.length !== 2 || !moduleOK(p[0]) || !isHash(p[1]) || has(out,p[0]))
        fail("MALFORMED_MIGRATION_BASELINE");
      out[p[0]] = p[1];
    }
    return out;
  }
  function stripLeanComments(s) {
    var out = "", i = 0, depth = 0, pair;
    while (i < s.length) {
      pair = s.substr(i, 2);
      if (pair === "/-") { depth++; out += "  "; i += 2; }
      else if (depth && pair === "-/") { depth--; out += "  "; i += 2; }
      else if (!depth && pair === "--") {
        while (i < s.length && s.charAt(i) !== "\n") { out += " "; i++; }
      } else { out += depth && s.charAt(i) !== "\n" ? " " : s.charAt(i); i++; }
    }
    if (depth) fail("UNTERMINATED_SOURCE_COMMENT");
    return out;
  }
  function importsOf(text) {
    var a = lines(stripLeanComments(text)), out = [], i, m, names, j;
    for (i = 0; i < a.length; i++) {
      m = /^\s*(?:(?:public|meta)\s+)*import\s+(.+)$/.exec(a[i]);
      if (!m) continue;
      names = trim(m[1]).split(/\s+/);
      for (j = 0; j < names.length; j++) {
        if (!moduleOK(names[j])) fail("UNSUPPORTED_IMPORT_SYNTAX");
        out.push(names[j]);
      }
    }
    return out;
  }
  function sourceClosureMatches(name, current, baseline, visited) {
    visited = visited || {};
    if (has(visited,name)) return true;
    visited[name] = true;
    var m = current[name], i;
    if (!m || !has(baseline,name) || baseline[name] !== m.sha) return false;
    for (i = 0; i < m.deps.length; i++)
      if (!sourceClosureMatches(m.deps[i], current, baseline, visited)) return false;
    return true;
  }
  function inputText(config, m, envHash, deps) {
    var out = "schema\t" + config.schema + "\ntarget\tLOCAL_COMPILER\n" +
      "module\t" + m.name + "\nsource\t" + m.sha + "\nenvironment\t" + envHash +
      "\ncompile_options\t-j 16 -E hasSorry\nchecker_options\t-v NAMED_MODULE\n";
    var names = sortedKeys(deps), i, d;
    for (i = 0; i < names.length; i++) {
      d = deps[names[i]];
      out += "dependency\t" + names[i] + "\t" + d.key + "\t" + d.digest + "\n";
    }
    return out;
  }
  function parseReceipt(text) {
    var a = lines(text), r = {artifacts:{}}, fields = {}, i, p;
    var allowed = {schema:1,target:1,module:1,source:1,environment:1,key:1,kind:1,log:1,input:1,audit:1};
    for (i = 0; i < a.length; i++) {
      if (!a[i]) continue;
      p = a[i].split("\t");
      if (p[0] === "artifact") {
        if (p.length !== 3 || !/^object\.(olean(?:\.private|\.server)?|ir)$/.test(p[1]) ||
            !isHash(p[2]) || has(r.artifacts,p[1])) fail("MALFORMED_ARTIFACT_RECEIPT");
        r.artifacts[p[1]] = p[2];
      } else {
        if (p.length !== 2 || !has(allowed,p[0]) || has(fields,p[0])) fail("MALFORMED_RECEIPT_FIELD");
        fields[p[0]] = true; r[p[0]] = p[1];
      }
    }
    var required = sortedKeys(allowed);
    for (i = 0; i < required.length; i++) if (!has(fields,required[i])) fail("INCOMPLETE_RECEIPT");
    if (!moduleOK(r.module) || !isHash(r.source) || !isHash(r.environment) || !isHash(r.key) ||
        !isHash(r.log) || !isHash(r.input) || !has(r.artifacts,"object.olean") ||
        (has(r.artifacts,"object.olean.private") && !has(r.artifacts,"object.olean.server")) ||
        !/^(COMPILE|KERNEL_RECHECK)$/.test(r.kind) || !/^(NONE|PASSED)$/.test(r.audit))
      fail("INVALID_RECEIPT");
    return r;
  }
  function receiptText(r) {
    var fields = ["schema","target","module","source","environment","key","kind","log","input","audit"], out="",i,ks;
    for (i=0;i<fields.length;i++) out+=fields[i]+"\t"+r[fields[i]]+"\n";
    ks=sortedKeys(r.artifacts);
    for (i=0;i<ks.length;i++) out+="artifact\t"+ks[i]+"\t"+r.artifacts[ks[i]]+"\n";
    return out;
  }
  function exactLine(text, expected) { var a=lines(text),i; for(i=0;i<a.length;i++) if(a[i]===expected) return true; return false; }
  function uniqueLogValue(text, prefix) {
    var a=lines(text),result=null,i;
    for(i=0;i<a.length;i++) if(a[i].substr(0,prefix.length)===prefix) {
      if(result!==null) fail("AMBIGUOUS_LEGACY_LOG_FIELD");
      result=a[i].substr(prefix.length);
    }
    return result;
  }
  function artifactSuffixes() { return [".olean", ".olean.server", ".olean.private", ".ir"]; }
  function artifactPath(base,suffix) { return base.replace(/\.olean$/,"")+suffix; }

  function runCache(h, config) {
    var pkg=h.abs(config.packageRoot), build=h.join(pkg,".build"), logPath=h.join(pkg,"GOODWORKFLOWFRONTIER_"+config.version+".log");
    var lock=null, locked=false, logReady=false, started=false, committed=false, before=null, envSpec=null;
    var pending=[], accepted={}, compiled=0,reused=0,rechecked=0,problem=null;
    var stage,logs,scratch,cache,plan,mods={},baseline,lean,checker,envHash,oldRoots=[],runStamp=h.stamp();
    function emit(s) { h.log(s); if(logReady) h.append(logPath,s+"\r\n"); }
    function hashText(s,label) { var f=h.join(scratch,label+".txt"); h.write(f,s); return h.hashFile(f); }
    function walk(root,choose,dict) {
      if(!h.dirExists(root)) fail("ENVIRONMENT_DIRECTORY_MISSING="+root);
      var fs=h.listFiles(root),ds=h.listDirs(root),i;
      for(i=0;i<fs.length;i++) if(choose(fs[i])) dict[h.abs(fs[i]).toLowerCase()]=h.abs(fs[i]);
      for(i=0;i<ds.length;i++) walk(ds[i],choose,dict);
    }
    function discoverExternal() {
      var roots=[h.join(envSpec.runtime,"lib\\lean")], scanRoots=roots.slice(0), metadata=[h.join(envSpec.mathdir,"lean-toolchain"),h.join(envSpec.mathdir,"lake-manifest.json"),h.join(envSpec.cacheRoot,"lake-manifest.json")];
      var containers=[h.join(envSpec.cacheRoot,".lake\\packages"),h.join(envSpec.mathdir,".lake\\packages")],seen={},i,j,ds,p,lib;
      seen[roots[0].toLowerCase()]=true;
      for(i=0;i<containers.length;i++) if(h.dirExists(containers[i])) {
        ds=h.listDirs(containers[i]).sort();
        for(j=0;j<ds.length;j++) {
          lib=h.join(ds[j],".lake\\build\\lib");p=h.join(lib,"lean");
          if(h.dirExists(p)&&!has(seen,p.toLowerCase())) {roots.push(p);seen[p.toLowerCase()]=true;}
          if(h.dirExists(lib)) scanRoots.push(lib);
          metadata.push(h.join(ds[j],"lean-toolchain"));metadata.push(h.join(ds[j],"lake-manifest.json"));
        }
      }
      if(!has(seen,envSpec.mathlib.toLowerCase())) roots.push(envSpec.mathlib);
      return {roots:roots,scanRoots:scanRoots,metadata:metadata};
    }
    function snapshot(label) {
      var discovered=discoverExternal();
      var d={},i,j,paths,rows=[],roots=discovered.scanRoots,metadata=discovered.metadata;
      function artifact(p) { return /(?:\.olean(?:\.private|\.server)?|\.ir|\.dll)$/i.test(p); }
      for(i=0;i<roots.length;i++) walk(roots[i],artifact,d);
      var bins=h.listFiles(envSpec.bin);
      for(i=0;i<bins.length;i++) if(/\.(exe|dll)$/i.test(bins[i])) d[h.abs(bins[i]).toLowerCase()]=h.abs(bins[i]);
      rows.push("format\tFULL_EXTERNAL_ENVIRONMENT_V1");
      rows.push("lean_path_roots\t"+envSpec.roots.join(";"));
      rows.push("discovered_external_roots\t"+discovered.roots.join(";"));
      rows.push("discovered_scan_roots\t"+roots.join(";"));
      rows.push("native_lean\t"+lean);
      rows.push("native_checker\t"+checker);
      rows.push("lean_sysroot\t"+envSpec.runtime);
      for(i=0;i<metadata.length;i++) {
        if(h.fileExists(metadata[i])) d[h.abs(metadata[i]).toLowerCase()]=h.abs(metadata[i]);
        else rows.push("absent\t"+h.abs(metadata[i]));
      }
      paths=sortedKeys(d);
      emit("ENVIRONMENT_HASH_BEGIN="+label+" FILES="+paths.length);
      var files=[],hashes=[],startTime=new Date().getTime();
      for(i=0;i<paths.length;i++) files.push(d[paths[i]]);
      if(typeof h.hashFiles==="function") {
        hashes=h.hashFiles(files,scratch,label,function(done,total) {
          emit("ENVIRONMENT_HASH_PROGRESS="+label+" "+done+"/"+total);
        },emit);
      } else {
        for(i=0;i<files.length;i++) {
          hashes.push(h.hashFile(files[i]));
          if((i+1)%200===0) emit("ENVIRONMENT_HASH_PROGRESS="+label+" "+(i+1)+"/"+files.length);
        }
      }
      if(!hashes || hashes.length!==files.length) fail("BATCH_HASH_RESULT_COUNT_MISMATCH");
      for(i=0;i<files.length;i++) {
        if(typeof hashes[i]!=="string" || !isHash(hashes[i])) fail("BATCH_HASH_INVALID_DIGEST="+i);
        rows.push("file\t"+files[i]+"\t"+hashes[i]);
      }
      emit("ENVIRONMENT_HASH_DONE="+label+" FILES="+files.length+" ELAPSED_MS="+(new Date().getTime()-startTime));
      var text=rows.join("\n")+"\n", file=h.join(logs,"environment_"+label+".tsv");
      h.write(file,text);
      return {hash:h.hashFile(file),text:text,file:file};
    }
    function sourcePath(m) { return h.join(pkg,m.rel.replace(/\//g,"\\")); }
    function objectPath(m) { return h.join(stage,m.name.replace(/\./g,"\\")+".olean"); }
    function validateReceipt(dir,m,key,input) {
      var receiptFile=h.join(dir,"receipt.tsv");
      if(!h.fileExists(receiptFile)) fail("CACHE_RECEIPT_MISSING="+m.name);
      var r=parseReceipt(h.read(receiptFile)),ks=sortedKeys(r.artifacts),i,files=h.listFiles(dir);
      if(r.schema!==config.schema || r.target!=="LOCAL_COMPILER" || r.module!==m.name ||
          r.source!==m.sha || r.environment!==envHash || r.key!==key ||
          h.read(h.join(dir,"input.txt"))!==input || r.input!==h.hashFile(h.join(dir,"input.txt"))) fail("CACHE_INPUT_MISMATCH="+m.name);
      if(h.hashFile(h.join(dir,"source.lean"))!==m.sha || h.hashFile(h.join(dir,"build.log"))!==r.log) fail("CACHE_SOURCE_OR_LOG_MISMATCH="+m.name);
      for(i=0;i<ks.length;i++) if(h.hashFile(h.join(dir,ks[i]))!==r.artifacts[ks[i]]) fail("CACHE_OBJECT_MISMATCH="+m.name);
      for(i=0;i<files.length;i++) {
        var bn=files[i].replace(/^.*[\\\/]/,"");
        if(/^object\./.test(bn) && !has(r.artifacts,bn)) fail("UNRECORDED_CACHE_ARTIFACT="+m.name);
      }
      if(m.name===config.auditModule && (r.audit!=="PASSED" || !exactLine(h.read(h.join(dir,"build.log")),config.auditMarker))) fail("CACHED_AUDIT_MISSING="+m.name);
      return {r:r,digest:h.hashFile(receiptFile),key:key,dir:dir};
    }
    function stageAccepted(m,entry) {
      var ks=sortedKeys(entry.r.artifacts),i,out=objectPath(m);
      h.mkdir(h.parent(out));
      for(i=0;i<ks.length;i++) h.copy(h.join(entry.dir,ks[i]),artifactPath(out,ks[i].substr("object".length)));
      for(i=0;i<ks.length;i++) if(h.hashFile(artifactPath(out,ks[i].substr("object".length)))!==entry.r.artifacts[ks[i]]) fail("STAGED_OBJECT_MISMATCH="+m.name);
    }
    function verifyAccepted(name) {
      var e=accepted[name],m=mods[name],ks,i;
      if(!e) fail("UNACCEPTED_PROJECT_DEPENDENCY="+name);
      if(h.hashFile(sourcePath(m))!==m.sha) fail("SOURCE_CHANGED_DURING_RUN="+name);
      ks=sortedKeys(e.r.artifacts);
      var suffixes=artifactSuffixes();
      for(i=0;i<suffixes.length;i++) if(h.fileExists(artifactPath(objectPath(m),suffixes[i]))!==has(e.r.artifacts,"object"+suffixes[i])) fail("STAGED_ARTIFACT_SET_CHANGED="+name);
      for(i=0;i<ks.length;i++) if(h.hashFile(artifactPath(objectPath(m),ks[i].substr("object".length)))!==e.r.artifacts[ks[i]]) fail("PROJECT_DEPENDENCY_CHANGED="+name);
    }
    function dependencies(m) {
      var out={},names=m.name===config.auditModule?sortedKeys(accepted):m.deps,i;
      for(i=0;i<names.length;i++) { verifyAccepted(names[i]); out[names[i]]=accepted[names[i]]; }
      return out;
    }
    function legacyCandidate(m) {
      var i,j,r,pp,rows,oldmap,oldlog,text,sourceLine,objectLine,out,artifacts,sourceHash,oldRow;
      if(m.name===config.auditModule) return null;
      for(i=0;i<oldRoots.length;i++) {
        r=oldRoots[i]; pp=h.join(r,"sources.tsv");
        if(!h.fileExists(pp)) continue;
        rows=parsePlan(h.read(pp)); oldmap={};
        for(j=0;j<rows.length;j++) oldmap[rows[j].name]=rows[j].sha;
        if(!sourceClosureMatches(m.name,mods,oldmap)) continue;
        oldlog=null;
        var oldfiles=h.listFiles(r);
        for(j=0;j<oldfiles.length;j++) if(/GOODWORKFLOWFRONTIER_v0_1_[23]\.log$/i.test(oldfiles[j])) {
          if(oldlog!==null) fail("AMBIGUOUS_LEGACY_MAIN_LOG="+r);
          oldlog=oldfiles[j];
        }
        if(!oldlog) continue;
        text=h.read(oldlog);
        if(!exactLine(text,"TARGET=LOCAL_COMPILER") || !exactLine(text,"COMPILE_PASS="+m.name)) continue;
        sourceLine=uniqueLogValue(text,"SOURCE_SHA256="+m.name+" ");
        objectLine=uniqueLogValue(text,"NATIVE_OBJECT_SHA256="+m.name+" ");
        if(sourceLine===null || objectLine===null || sourceLine.substr(0,64)!==m.sha || !isHash(objectLine)) fail("LEGACY_LOG_LINKAGE_INVALID="+m.name);
        if(h.hashFile(h.join(r,m.rel.replace(/\//g,"\\")))!==m.sha) fail("LEGACY_SOURCE_CHANGED="+m.name);
        out=h.join(r,".build\\lib\\lean\\"+m.name.replace(/\./g,"\\")+".olean");
        if(!h.fileExists(out)) fail("LEGACY_ARTIFACT_MISSING="+out);
        if(h.hashFile(out)!==objectLine) fail("LEGACY_OBJECT_CHANGED="+m.name);
        artifacts={"object.olean":objectLine};
        var sides=["private","server"],line,sp;
        for(j=0;j<sides.length;j++) {
          line=uniqueLogValue(text,"CONTEXT_SHA256=NATIVE_OBJECT_"+sides[j].toUpperCase()+"_"+m.name+" ");
          sp=out+"."+sides[j];
          if((line!==null)!==h.fileExists(sp)) fail("LEGACY_SIDECAR_PRESENCE_MISMATCH="+m.name+"."+sides[j]);
          if(line!==null) {
            if(!isHash(line.substr(0,64)) || h.hashFile(sp)!==line.substr(0,64)) fail("LEGACY_SIDECAR_HASH_MISMATCH="+m.name);
            artifacts["object.olean."+sides[j]]=line.substr(0,64);
          }
        }
        if(has(artifacts,"object.olean.private")&&!has(artifacts,"object.olean.server")) fail("LEGACY_PRIVATE_WITHOUT_SERVER="+m.name);
        return {root:r,object:out,artifacts:artifacts,log:oldlog};
      }
      return null;
    }
    function makePending(m,key,input,nativeLog,kind,legacy) {
      var dir=h.join(scratch,"pending_"+key), r={schema:config.schema,target:"LOCAL_COMPILER",module:m.name,source:m.sha,environment:envHash,key:key,kind:kind,audit:"NONE",artifacts:{}},i,suffs=artifactSuffixes(),p;
      h.mkdir(dir);h.copy(sourcePath(m),h.join(dir,"source.lean")); h.copy(nativeLog,h.join(dir,"build.log"));h.write(h.join(dir,"input.txt"),input);
      r.log=h.hashFile(h.join(dir,"build.log"));r.input=h.hashFile(h.join(dir,"input.txt"));
      for(i=0;i<suffs.length;i++) {
        p=artifactPath(objectPath(m),suffs[i]);
        if(h.fileExists(p)) { h.copy(p,h.join(dir,"object"+suffs[i]));r.artifacts["object"+suffs[i]]=h.hashFile(p); }
      }
      if(!has(r.artifacts,"object.olean")) fail("NATIVE_OBJECT_MISSING="+m.name);
      if(m.name===config.auditModule) {
        if(!exactLine(h.read(nativeLog),config.auditMarker)) fail("INDEPENDENT_AXIOM_AUDIT_ACCEPTANCE_MISSING");
        r.audit="PASSED";
      }
      if(legacy) {
        h.copy(legacy.log,h.join(dir,"legacy_main.log"));
        h.write(h.join(dir,"legacy_provenance.txt"),"LEGACY_ROOT="+legacy.root+"\nLEGACY_LOG_SHA256="+h.hashFile(legacy.log)+"\nNEW_ACCEPTANCE=KERNEL_RECHECK_CURRENT_ENVIRONMENT\nHISTORICAL_FULL_ENVIRONMENT_FINGERPRINT=NOT_ASSERTED\n");
      }
      h.write(h.join(dir,"receipt.tsv"),receiptText(r));
      var entry=validateReceipt(dir,m,key,input);
      return entry;
    }
    function moduleStep(m) {
      if(h.hashFile(sourcePath(m))!==m.sha) fail("SOURCE_CHANGED_BEFORE_MODULE="+m.name);
      var deps=dependencies(m),input=inputText(config,m,envHash,deps),key=hashText(input,"input_"+m.name),dir=h.join(cache,key),e,legacy,nativeLog=h.join(logs,m.name+".log"),out=objectPath(m),ks,i;
      if(h.dirExists(dir)) {
        e=validateReceipt(dir,m,key,input);stageAccepted(m,e);accepted[m.name]=e;reused++;
        emit("REUSE="+m.name);return;
      }
      legacy=legacyCandidate(m);
      h.mkdir(h.parent(out));
      if(legacy) {
        if(!h.fileExists(checker)) fail("NATIVE_LEANCHECKER_MISSING_NO_RECOMPILATION="+m.name);
        ks=sortedKeys(legacy.artifacts);
        for(i=0;i<ks.length;i++) h.copy(artifactPath(legacy.object,ks[i].substr("object".length)),artifactPath(out,ks[i].substr("object".length)));
        emit("KERNEL_RECHECK_EXISTING_OBJECT="+m.name);
        var checkExit=h.run(checker,["-v",m.name],nativeLog);
        h.append(logPath,"NATIVE_LOG_BEGIN="+m.name+"\r\n"+h.read(nativeLog)+"\r\nNATIVE_LOG_END="+m.name+"\r\n");
        if(checkExit!==0) {h.log(h.read(nativeLog));fail("LEGACY_KERNEL_RECHECK_FAILED="+m.name);}
        if(!exactLine(h.read(nativeLog),"replaying "+m.name)) fail("CHECKER_TARGET_CONFIRMATION_MISSING="+m.name);
        for(i=0;i<ks.length;i++) if(h.hashFile(artifactPath(out,ks[i].substr("object".length)))!==legacy.artifacts[ks[i]]) fail("OBJECT_CHANGED_DURING_RECHECK="+m.name);
        e=makePending(m,key,input,nativeLog,"KERNEL_RECHECK",legacy);rechecked++;
      } else {
        if(sourceClosureMatches(m.name,mods,baseline)) fail("LEGACY_ARTIFACTS_REQUIRED="+m.name+"; keep previous package folders or set GPKQ_PREVIOUS_ROOT");
        emit("COMPILE_NEW_OR_INVALIDATED="+m.name);
        var compileExit=h.run(lean,["-j","16","-E","hasSorry","-o",out,sourcePath(m)],nativeLog);
        h.append(logPath,"NATIVE_LOG_BEGIN="+m.name+"\r\n"+h.read(nativeLog)+"\r\nNATIVE_LOG_END="+m.name+"\r\n");
        if(compileExit!==0) {h.log(h.read(nativeLog));fail("NATIVE_LEAN_COMPILATION_FAILED="+m.name);}
        if(/sorryAx|error:/i.test(h.read(nativeLog))) fail("COMPILER_ERROR_OR_SORRYAX="+m.name);
        e=makePending(m,key,input,nativeLog,"COMPILE",null);compiled++;
      }
      if(h.hashFile(sourcePath(m))!==m.sha) fail("SOURCE_CHANGED_DURING_MODULE="+m.name);
      dependencies(m);
      accepted[m.name]=e;
      pending.push({dir:e.dir,key:key,module:m.name});
      emit("ACCEPTED="+m.name+" KIND="+e.r.kind+" RECEIPT="+e.digest);
    }
    function initialize() {
      h.mkdir(build);
      var user=h.env("USERPROFILE"),root=h.env("GPKQ_ANCHOR_ROOT")||h.join(user,"lean-native\\LEAN_ANCHORINGS\\GPKQBKQRXYTENSORHOPF_ODD_ZETA");
      h.mkdir(root);lock=h.join(root,"active.lock");h.createLock(lock);locked=true;
      h.write(logPath,"PACKAGE="+config.packageName+"\r\n");logReady=true;
      emit("BRANCH=GPKQBKQRXYTENSORHOPF_ODD_ZETA");emit("MODE=A_TIER_LEAN");emit("TARGET=LOCAL_COMPILER");emit("RUNNER=NATIVE_WINDOWS_INCREMENTAL_RECEIPTS");
      cache=h.join(root,"receipts_v1");h.mkdir(cache);
      var runroot=h.join(build,"run_"+runStamp);if(h.dirExists(runroot)) fail("RUN_DIRECTORY_COLLISION");h.mkdir(runroot);
      stage=h.join(runroot,"lib\\lean");logs=h.join(runroot,"logs");scratch=h.join(runroot,"scratch");h.mkdir(stage);h.mkdir(logs);h.mkdir(scratch);
      var pp=h.join(pkg,"sources.tsv"),bp=h.join(pkg,"migration_required.tsv"),i,j,im,p,seen={};
      if(h.hashFile(pp)!==config.planHash||h.hashFile(bp)!==config.migrationHash) fail("PACKAGE_PLAN_INTEGRITY_FAILED");
      plan=parsePlan(h.read(pp));baseline=parseBaseline(h.read(bp));
      if(plan.length!==43) fail("MODULE_COUNT_MISMATCH");
      for(i=0;i<plan.length;i++) mods[plan[i].name]=plan[i];
      for(i=0;i<plan.length;i++) {
        if(h.hashFile(sourcePath(plan[i]))!==plan[i].sha) fail("SOURCE_INTEGRITY_FAILED="+plan[i].name);
        im=importsOf(h.read(sourcePath(plan[i])));plan[i].deps=[];
        for(j=0;j<im.length;j++) if(has(mods,im[j])) {
          if(!has(seen,im[j])) fail("IMPORT_ORDER_INVALID="+plan[i].name);
          plan[i].deps.push(im[j]);
        }
        seen[plan[i].name]=true;
      }
      emit("PACKAGE_SOURCE_INTEGRITY=PASS");
      lean=h.env("LEAN433_EXE")||h.join(user,".elan\\toolchains\\leanprover--lean4---v4.33.0\\bin\\lean.exe");lean=h.abs(lean);
      if(!h.fileExists(lean)) fail("NATIVE_LEAN_433_EXE_MISSING_SET_LEAN433_EXE");
      var bin=h.parent(lean),runtime=h.parent(bin);checker=h.join(bin,"leanchecker.exe");
      if(!h.fileExists(h.join(runtime,"lib\\lean\\Init.olean"))) fail("NATIVE_LEAN_CORE_MISSING");
      var cacheRoot=h.env("GPKQ_CACHE_ROOT")||h.join(user,"lean-native\\awpi_phi_rh_lean_sieved_v0_1_1");
      if(!h.env("GPKQ_CACHE_ROOT")&&!h.fileExists(h.join(cacheRoot,".lake\\packages\\mathlib\\.lake\\build\\lib\\lean\\Mathlib.olean"))) cacheRoot=h.join(user,"lean-native\\zetahyperbolic_10_stage_stitch_lean433_cache");
      var mathdir=h.join(cacheRoot,".lake\\packages\\mathlib"),mathlib=h.join(mathdir,".lake\\build\\lib\\lean"),roots=[h.join(runtime,"lib\\lean")],metadata=[h.join(mathdir,"lean-toolchain"),h.join(mathdir,"lake-manifest.json"),h.join(cacheRoot,"lake-manifest.json")];
      if(!h.fileExists(h.join(mathlib,"Mathlib.olean"))||trim(h.read(h.join(mathdir,"lean-toolchain")))!=="leanprover/lean4:v4.33.0") fail("CACHED_MATHLIB_TOOLCHAIN_OR_OBJECT_MISSING");
      envSpec={bin:bin,runtime:runtime,cacheRoot:cacheRoot,mathdir:mathdir,mathlib:mathlib};
      envSpec.roots=discoverExternal().roots;roots=envSpec.roots;
      h.setEnv("LEAN_SYSROOT",runtime);h.setEnv("LEAN_PATH",[stage].concat(roots).join(";"));h.setEnv("LEAN_SRC_PATH","");h.setCwd(h.join(pkg,"src"));
      var versionLog=h.join(logs,"lean-version.log");
      if(h.run(lean,["--version"],versionLog)!==0 || !/version 4\.33\.0,/.test(h.read(versionLog))) fail("NATIVE_LEAN_MUST_BE_EXACTLY_4_33_0");
      emit("LEAN_VERSION="+trim(h.read(versionLog)));emit("ANCHOR_ROOT="+root);
      var parent=h.parent(pkg),versions=["v0_1_3","v0_1_2"],prev=h.env("GPKQ_PREVIOUS_ROOT");
      if(prev) oldRoots.push(h.abs(prev));
      for(i=0;i<versions.length;i++) {
        p=h.join(parent,"GPKQBKQRXYTENSORHOPF_ODD_ZETA_PRIMITIVE_GROWTH_LEAN_"+versions[i]+"_construction");
        if(h.dirExists(p)) oldRoots.push(p);
      }
      before=snapshot("before");envHash=before.hash;started=true;emit("ENVIRONMENT_SHA256="+envHash);
    }
    try {
      initialize();
      var i;
      for(i=0;i<plan.length;i++) moduleStep(plan[i]);
      if(plan[plan.length-1].name!==config.auditModule || !accepted[config.auditModule] || accepted[config.auditModule].r.audit!=="PASSED") fail("FINAL_AXIOM_AUDIT_NOT_ACCEPTED");
    } catch(e) { problem=e; }
    if(started) {
      try {
        var names=sortedKeys(accepted),j;
        for(j=0;j<names.length;j++) verifyAccepted(names[j]);
        var after=snapshot("after");
        if(after.hash!==before.hash || after.text!==before.text) fail("EXTERNAL_ENVIRONMENT_CHANGED_NO_RECEIPTS_COMMITTED");
        for(j=0;j<pending.length;j++) {
          if(!has(accepted,pending[j].module) || accepted[pending[j].module].key!==pending[j].key) fail("UNACCEPTED_PENDING_RECEIPT");
          var dest=h.join(cache,pending[j].key);
          if(h.dirExists(dest)) fail("CACHE_COMMIT_COLLISION");
          h.moveDir(pending[j].dir,dest);
        }
        committed=true;emit("SUCCESSFUL_MODULE_RECEIPTS_PRESERVED="+pending.length);
      } catch(e2) { problem=e2; }
    }
    var result={compiled:compiled,reused:reused,rechecked:rechecked,committed:committed,ok:!problem};
    emit("MODULES_COMPILED="+compiled);emit("MODULES_REUSED="+reused);emit("MODULES_KERNEL_RECHECKED="+rechecked);
    if(problem) {result.error=String(problem.message||problem);emit("BUILD=FAIL");emit("REASON="+result.error);}
    else {emit("BUILD=PASS");emit("AXIOM_AUDIT=PASS_INDEPENDENT_KERNEL_WALK");emit("PROOF_SCOPE=SHARED_SEQUENCE_BASE_AND_STEP_CONDITIONAL");emit("UNCONDITIONAL_ALL_ODD_ZETA_IRRATIONALITY=NOT_CLAIMED");}
    if(logReady) emit("LOG="+logPath);else h.log("CANONICAL_LOG_UNTOUCHED=EARLY_FAILURE");
    if(locked) {
      try {h.removeDir(lock);} catch(e3) {
        result.ok=false;result.error="LOCK_RELEASE_FAILED="+String(e3.message||e3);
        emit("CACHE_LOCK_RELEASE=FAIL");emit("RUNNER_EXIT=FAIL_LOCK_RELEASE");emit("REASON="+result.error);
      }
    }
    return result;
  }

  function windowsHost(config) {
    var fso=new ActiveXObject("Scripting.FileSystemObject"), shell=new ActiveXObject("WScript.Shell"),env=shell.Environment("PROCESS");
    var cert=env("SystemRoot")+"\\System32\\certutil.exe",comspec=env("ComSpec");
    function safe(s) {if(/[\r\n%!"]/.test(s)) fail("UNSUPPORTED_PATH_CHARACTER="+s);return s;}
    function q(s) {return '"'+safe(String(s))+'"';}
    function mkdir(p) { if(fso.FolderExists(p)) return;var parent=fso.GetParentFolderName(p);if(parent&&!fso.FolderExists(parent))mkdir(parent);fso.CreateFolder(p); }
    function read(p) {var x=fso.OpenTextFile(p,1,false);try{return x.ReadAll();}finally{x.Close();}}
    function write(p,s,append) {mkdir(fso.GetParentFolderName(p));var x=fso.OpenTextFile(p,append?8:2,true,0);try{x.Write(s);}finally{x.Close();}}
    function list(p,dirs) {var a=[],e=new Enumerator(dirs?fso.GetFolder(p).SubFolders:fso.GetFolder(p).Files);for(;!e.atEnd();e.moveNext())a.push(e.item().Path);return a.sort();}
    function hashFile(p) {
      if(!fso.FileExists(p))fail("HASH_FILE_MISSING="+p);
      var proc=shell.Exec(q(cert)+" -hashfile "+q(p)+" SHA256"),out=proc.StdOut.ReadAll(),err=proc.StdErr.ReadAll(),a=lines(out),found=null,i,v;
      while(proc.Status===0) WScript.Sleep(1);
      if(proc.ExitCode!==0)fail("CERTUTIL_HASH_FAILED="+p);
      for(i=0;i<a.length;i++){v=a[i].replace(/\s/g,"").toLowerCase();if(isHash(v)){if(found!==null)fail("AMBIGUOUS_SHA256");found=v;}}
      if(found===null)fail("SHA256_OUTPUT_MISSING="+p);return found;
    }
    function command(exe,args) {var a=[q(exe)],i;for(i=0;i<args.length;i++)a.push(q(args[i]));return a.join(" ");}
    function runProgram(exe,args,log) {return shell.Run(q(comspec)+' /d /s /c "'+command(exe,args)+" >"+q(log)+' 2>&1"',0,true);}
    function streamProgram(exe,args,onLine) {
      // Merge stderr into stdout so neither child pipe can fill while we drain the other.
      var proc=shell.Exec(q(comspec)+' /d /s /c "'+command(exe,args)+' 2>&1"');
      try {while(!proc.StdOut.AtEndOfStream) onLine(proc.StdOut.ReadLine());}
      catch(e) {try {proc.Terminate();} catch(ignored) {} throw e;}
      while(proc.Status===0) WScript.Sleep(10);
      return proc.ExitCode;
    }
    function writeUnicode(p,s) {var x=fso.CreateTextFile(p,false,true);try{x.Write(s);}finally{x.Close();}}
    var batchPrepared=false,batchAvailable=false,batchExe=null,batchExeHash=null,batchSource=null,batchWorkers=4;
    function prepareBatch(scratch,emit) {
      if(batchPrepared) return;
      batchSource=fso.BuildPath(config.packageRoot,"NativeBatchHash.cs");
      if(!isHash(config.hashSourceHash) || hashFile(batchSource)!==config.hashSourceHash) fail("BATCH_HASH_SOURCE_INTEGRITY_FAILED");
      var workerText=env("GPKQ_HASH_WORKERS");
      if(workerText) {
        if(!/^(?:[1-9]|1[0-6])$/.test(workerText)) fail("GPKQ_HASH_WORKERS_MUST_BE_1_TO_16");
        batchWorkers=Number(workerText);
      }
      var framework=fso.BuildPath(env("SystemRoot"),"Microsoft.NET"),candidates=[
        fso.BuildPath(framework,"Framework64\\v4.0.30319\\csc.exe"),
        fso.BuildPath(framework,"Framework\\v4.0.30319\\csc.exe")],compiler=null,i;
      for(i=0;i<candidates.length;i++) if(fso.FileExists(candidates[i])) {compiler=candidates[i];break;}
      if(!compiler) {
        emit("HASH_ACCELERATOR=UNAVAILABLE_FRAMEWORK_CSC_MISSING");
        batchPrepared=true;return;
      }
      batchExe=fso.BuildPath(scratch,"native_batch_hash.exe");
      var compileLog=fso.BuildPath(scratch,"native_batch_hash_compile.log"),frameworkDir=fso.GetParentFolderName(compiler),
          mscorlib=fso.BuildPath(frameworkDir,"mscorlib.dll"),system=fso.BuildPath(frameworkDir,"System.dll"),systemCore=fso.BuildPath(frameworkDir,"System.Core.dll");
      if(!fso.FileExists(mscorlib) || !fso.FileExists(system) || !fso.FileExists(systemCore)) fail("BATCH_HASH_FRAMEWORK_REFERENCES_MISSING");
      if(fso.FileExists(batchExe)) fail("BATCH_HASH_EXECUTABLE_ALREADY_EXISTS");
      emit("HASH_ACCELERATOR_PREPARE=OFFLINE_FRAMEWORK_CSC");
      if(runProgram(compiler,["/nologo","/noconfig","/nostdlib+","/target:exe","/optimize+","/reference:"+mscorlib,"/reference:"+system,"/reference:"+systemCore,"/out:"+batchExe,batchSource],compileLog)!==0 || !fso.FileExists(batchExe))
        fail("BATCH_HASH_COMPILER_FAILED_LOG="+compileLog);
      if(hashFile(batchSource)!==config.hashSourceHash) fail("BATCH_HASH_SOURCE_CHANGED_DURING_COMPILATION");
      batchExeHash=hashFile(batchExe);
      var selfLines=[],selfExit=streamProgram(batchExe,["--self-test"],function(s){selfLines.push(s);});
      if(selfExit!==0 || selfLines.length!==1 || selfLines[0]!=="HASH_SELF_TEST=PASS") fail("BATCH_HASH_SELF_TEST_FAILED");
      if(hashFile(batchExe)!==batchExeHash) fail("BATCH_HASH_EXECUTABLE_CHANGED");
      batchAvailable=true;batchPrepared=true;
      emit("HASH_ACCELERATOR_SELF_TEST=PASS");
    }
    function hashFiles(files,scratch,label,onProgress,emit) {
      prepareBatch(scratch,emit);
      var i,out=[];
      if(!batchAvailable) {
        emit("ENVIRONMENT_HASH_ENGINE="+label+" CERTUTIL_SERIAL_COMPATIBILITY");
        for(i=0;i<files.length;i++) {
          out.push(hashFile(files[i]));
          if((i+1)%200===0 || i+1===files.length) onProgress(i+1,files.length);
        }
        return out;
      }
      emit("ENVIRONMENT_HASH_ENGINE="+label+" SHA256_BATCH WORKERS="+batchWorkers);
      if(hashFile(batchSource)!==config.hashSourceHash || hashFile(batchExe)!==batchExeHash) fail("BATCH_HASH_HELPER_CHANGED");
      if(!/^(before|after)$/.test(label)) fail("INVALID_BATCH_LABEL");
      var manifest=fso.BuildPath(scratch,"hash_files_"+label+".utf16"),output=fso.BuildPath(scratch,"hash_results_"+label+".tsv");
      if(fso.FileExists(manifest) || fso.FileExists(output)) fail("BATCH_HASH_OUTPUT_ALREADY_EXISTS");
      for(i=0;i<files.length;i++) if(/[\r\n\t]/.test(files[i])) fail("UNSUPPORTED_HASH_PATH");
      writeUnicode(manifest,files.join("\r\n")+(files.length?"\r\n":""));
      var manifestHash=hashFile(manifest),last=0,passes=0,protocolError=false,errorLine="",count=files.length;
      var rc=streamProgram(batchExe,[manifest,output,String(batchWorkers)],function(s) {
        var m=/^HASH_PROGRESS=(\d+)\/(\d+)$/.exec(s),done,total;
        if(m) {
          done=Number(m[1]);total=Number(m[2]);
          if(total!==count || done<=last || done>count) protocolError=true;
          else {last=done;onProgress(done,total);}
        } else if(s==="HASH_BATCH_PASS="+count) {passes++;}
        else {protocolError=true;errorLine=s;}
      });
      if(rc!==0) fail("BATCH_HASH_PROCESS_FAILED="+rc+" "+errorLine);
      if(protocolError || passes!==1 || last!==count) fail("BATCH_HASH_PROTOCOL_FAILED="+errorLine);
      if(hashFile(manifest)!==manifestHash || hashFile(batchSource)!==config.hashSourceHash || hashFile(batchExe)!==batchExeHash) fail("BATCH_HASH_INPUT_OR_HELPER_CHANGED");
      if(!fso.FileExists(output)) fail("BATCH_HASH_OUTPUT_MISSING");
      out=parseBatchHashes(read(output),count);
      // Independent native implementation checks actual file output on every batch.
      var probes=[0,Math.floor(count/2),count-1],seen={};
      for(i=0;i<probes.length;i++) if(probes[i]>=0 && probes[i]<count && !has(seen,String(probes[i]))) {
        seen[String(probes[i])]=true;
        if(hashFile(files[probes[i]])!==out[probes[i]]) fail("BATCH_HASH_CERTUTIL_CROSSCHECK_FAILED="+probes[i]);
      }
      emit("HASH_ACCELERATOR_CERTUTIL_CROSSCHECK="+label+" PASS");
      return out;
    }
    return {
      env:function(k){return env(k);},setEnv:function(k,v){env(k)=v;},setCwd:function(p){shell.CurrentDirectory=safe(p);},
      join:function(a,b){return safe(fso.BuildPath(a,b));},parent:function(p){return fso.GetParentFolderName(p);},abs:function(p){return safe(fso.GetAbsolutePathName(p));},
      fileExists:function(p){return fso.FileExists(p);},dirExists:function(p){return fso.FolderExists(p);},mkdir:mkdir,
      createLock:function(p){try{fso.CreateFolder(p);}catch(e){fail("CACHE_LOCK_EXISTS_OR_CANNOT_CREATE="+p);}},
      removeDir:function(p){fso.DeleteFolder(p,true);},copy:function(a,b){mkdir(fso.GetParentFolderName(b));fso.CopyFile(a,b,true);},moveDir:function(a,b){fso.MoveFolder(a,b);},
      read:read,write:function(p,s){write(p,s,false);},append:function(p,s){write(p,s,true);},listFiles:function(p){return list(p,false);},listDirs:function(p){return list(p,true);},
      hashFile:hashFile,hashFiles:hashFiles,run:runProgram,
      log:function(s){WScript.Echo(s);},stamp:function(){return String(new Date().getTime());}
    };
  }
  var api={parsePlan:parsePlan,parseBaseline:parseBaseline,parseBatchHashes:parseBatchHashes,stripLeanComments:stripLeanComments,importsOf:importsOf,sourceClosureMatches:sourceClosureMatches,inputText:inputText,parseReceipt:parseReceipt,receiptText:receiptText,exactLine:exactLine,uniqueLogValue:uniqueLogValue,runCache:runCache,windowsHost:windowsHost,config:DEFAULT_CONFIG};
  if(typeof module!=="undefined"&&module.exports) module.exports=api;
  else {
    try {
      if(WScript.Arguments.length!==1) fail("EXPECTED_PACKAGE_ROOT_ARGUMENT");
      DEFAULT_CONFIG.packageRoot=String(WScript.Arguments(0));
      var result=runCache(windowsHost(DEFAULT_CONFIG),DEFAULT_CONFIG);WScript.Quit(result.ok?0:1);
    } catch(e) {WScript.Echo("BUILD=FAIL\r\nREASON="+String(e.message||e));WScript.Quit(1);}
  }
}());
