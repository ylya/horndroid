package com.horndroid.printers;

public final class ReportWriterFactory {

    public static ReportPrinter getDefaultReportPrinter() {
        return new DefaultReportPrinter();
    }

    public static ReportPrinter getReportToJsonPrinter() {
        return new JsonReportPrinter();
    }
}
