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

Note: DYLD_LIBRARY_PATH (MAC OS) or LD_LIBRARY_PATH (Linux, FreeBSD) should include build target directory (see %Z3Home%../examples/java/README).

## Dependency Resolution:  apktool
Build apktool.jar to %apktool%:
http://ibotpeaches.github.io/Apktool/

Note: included by default in src/main/resources

# Build fsHD

` mvn clean package `

## Run fsHD

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
(SourcesAndSinksDroidSafe.txt) should be in src/main/resources/bin

You can specify a path to an *.apk file or a folder (all apps in sub-folders will be also analysed).

Example execution:
`java -jar fshorndroid-0.0.1.jar / ./ %home%/apksToTest`

For all *.apk files in the folder HornDroid will report (in logs/app.log):
- Horn clauses generation time;
- Analysis time;
- Taint tracking result: POSSIBLE LEAK if register might leak the sensitive data or NO LEAK if it does not. In addition it specifies the register number, the exact place where leakage happens and the sink.

## Publications:

*Sound Flow-Sensitive Heap Abstraction for the Static Analysis of Android Applications*
Stefano Calzavara, Ilya Grishchenko, Adrien Koutsos, and Matteo Maffei
In Proceedings of 30th Computer Security Foundations Symposium (IEEE CSF 2017).
[PDF](https://secpriv.tuwien.ac.at/fileadmin/t/secpriv/Papers/csf2017.pdf)
[Technical Report](https://secpriv.tuwien.ac.at/fileadmin/t/secpriv/Papers/csf2017-tr.pdf)
Technical report: 
*HornDroid: Practical and Sound Security Static Analysis of Android Applications by SMT Solving*
Stefano Calzavara, Ilya Grishchenko, and Matteo Maffei
In Proceedings of 1st IEEE European Symposium on Security and Privacy (IEEE EuroS&P 2016).
[PDF](https://secpriv.tuwien.ac.at/fileadmin/t/secpriv/Papers/eurosp16.pdf)
[Technical Report](https://secpriv.tuwien.ac.at/fileadmin/t/secpriv/Papers/eurosp16-tr.pdf)
