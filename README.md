![logo](/logo.png?raw=true "")

## Dependency Resolution:  Z3
Build Z3 to %Z3Home%:
https://github.com/Z3Prover/z3.git

### MAC OS
Copy libz3java.dylib from %Z3Home% to src/main/resources

### WINDOWS
Copy libz3.dll && z3.java.dll from %Z3Home% to src/main/resources
Note: These are included by default currently

### Other OS
Copy relevant library file from %Z3Home% to src/main/resources

## Dependency Resolution:  apktool
Build apktool.jar to %apktool%:
http://ibotpeaches.github.io/Apktool/

Note: included by default in src/main/resources

## Run

` java -jar fshorndroid-version.jar [options] '/' '%apktool%/' '<apk-file>' `
options:

-q precise query results;

-w sensitive array indexes;

-n bitvector size (default 64);

-i flow insensitive heap;

-r number of queries;

-d print debugging information (argument: integer 1 - taint information, 2 - localheap, or 3 - global heap);

-l stop after the first leak is found;

-s flow sensitive heap only for the objects created in the method that contains a call to a sink.

#### Note: files Callbacks.txt, EntryPoints.txt and SourcesAndSinks.txt 
(SourcesAndSinksDroidSafe.txt) should be in src/main/resources

You can specify a path to an *.apk file or a folder (all apps in sub-folders will be also analysed).

Example execution:
`java -jar fshorndroid-0.0.1.jar / ./ %home%/apksToTest`

For all *.apk files in the folder HornDroid will report:
- Horn clauses generation time;
- Analysis time;
- Taint tracking result: SAT if register leaks the sensitive data or UNSAT if it does not. In addition it specifies the register number, the exact place where leakage happens and the sink.