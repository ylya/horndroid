package com.horndroid.printers;

import com.horndroid.model.Report;
import com.horndroid.model.ReportEntry;

import java.util.List;


public final class DefaultReportPrinter extends ReportPrinter {


    protected String getReportInString(Report report) {
        int i = 1;
        String s = "";
        s += report.getTag() + " :\n";
        s += "Number of queries :" + report.getNumberOfQueries() + "\n";
        final List<ReportEntry> reportEntries = report.getReportEntries();
        for (ReportEntry reportEntry : reportEntries) {
            s += i + ": ";
            if (reportEntry.isVerbose())
                s += reportEntry.getDescription() + "\n";
            s += reportEntry.getResult() + "\n";
            i++;
        }
        return s;
    }


}
