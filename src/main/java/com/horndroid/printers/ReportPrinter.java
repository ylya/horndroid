package com.horndroid.printers;

import com.horndroid.exceptions.ReportWritingException;
import com.horndroid.model.Report;
import org.apache.commons.io.FileUtils;

import java.io.File;
import java.io.IOException;

/**
 * This report writer interface can be used to generate JSON/XML/Custom files
 * with report content
 *
 * @author Sharmeen
 */
public abstract class ReportPrinter {

    protected abstract String getReportInString(Report report) throws ReportWritingException;

    public void writeReportToFile(Report report, String filename) throws ReportWritingException {
        String s = getReportInString(report);
        try {
            FileUtils.writeStringToFile(new File(filename), s);
        } catch (IOException e) {
            throw new ReportWritingException("Problem writing report to file", e);
        }
    }

    public void printReport(Report report) throws ReportWritingException {
        String s = getReportInString(report);
        System.out.println(s);
    }

}
