package com.horndroid.model;

import java.util.ArrayList;
import java.util.List;

/**
 * Represents a report with the analysis details
 *
 * @author Sharmeen
 */
public class Report {

    private String tag;
    private int numberOfQueries;
    private List<ReportEntry> reportEntries = new ArrayList<>();

    public List<ReportEntry> getReportEntries() {
        return new ArrayList<>(reportEntries);
    }

    public void setReportEntries(List<ReportEntry> reportEntries) {
        this.reportEntries = new ArrayList<>(reportEntries);
    }

    public void addReportEntry(ReportEntry reportEntry) {
        reportEntries.add(reportEntry);
    }


    public int getNumberOfQueries() {
        return numberOfQueries;
    }

    public void setNumberOfQueries(int numberOfQueries) {
        this.numberOfQueries = numberOfQueries;
    }

    public String getTag() {
        return tag;
    }

    public void setTag(String tag) {
        this.tag = tag;
    }
}
