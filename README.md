# horndroid
![logo](/logo.png?raw=true "")

Build horndroid, depends on:
https://github.com/JesusFreke/smali.git

Build Z3 to %Z3Home%:
https://github.com/Z3Prover/z3.git

Build apktool.jar to %apktool%:
http://ibotpeaches.github.io/Apktool/

Run

java -jar horndroid.jar [options] %Z3Home%/bin %apktool%/ <apk-file>
options:

-q precise query results

-w sensitive array indexes

-s one query per file, run Z3 in parallel saving results to the /out folder

-n bitvector size (default 64)

Note: files Callbacks.txt, EntryPoints.txt and SourcesAndSinks.txt should be in the same folder.

You can specify a path to an *.apk file or a folder (all apps in sub-folders will be also analysed).
Resulting Horn Clauses are in *.smt2 file in the %appname% folder.

Example execution:
java -jar horndroid.jar %home%/z3/bin %apktool%/ %home%/apksToTest

For all *.apk files in the folder HornDroid will report:
- Horn clauses generation time;
- Analysis time;
- Taint tracking result: SAT if register leaks the sensitive data or UNSAT if it does not. In addition it specifies the register number, the exact place where leakage happens and the sink.
