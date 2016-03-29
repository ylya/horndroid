# horndroid
![logo](/logo.png?raw=true "")

Build Z3 to %Z3Home%:
https://github.com/Z3Prover/z3.git

Copy libz3java.dylib from %Z3Home% to the same folder as horndroid.jar.

Build apktool.jar to %apktool%:
http://ibotpeaches.github.io/Apktool/

Run

java -jar horndroid.jar [options] %Z3Home%/bin %apktool%/ <apk-file>
options:

-q precise query results;

-w sensitive array indexes;

-n bitvector size (default 64).

Note: files Callbacks.txt, EntryPoints.txt and SourcesAndSinks.txt (SourcesAndSinksDroidSafe.txt) should be in the same folder.

You can specify a path to an *.apk file or a folder (all apps in sub-folders will be also analysed).

Example execution:
java -jar horndroid.jar %home%/z3/bin %apktool%/ %home%/apksToTest

For all *.apk files in the folder HornDroid will report:
- Horn clauses generation time;
- Analysis time;
- Taint tracking result: SAT if register leaks the sensitive data or UNSAT if it does not. In addition it specifies the register number, the exact place where leakage happens and the sink.
