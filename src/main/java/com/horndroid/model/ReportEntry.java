package com.horndroid.model;

/**
 * Represents one entry in a report
 *
 */
public class ReportEntry {

    private String description;
    private String result;
    private boolean isVerbose;

    public ReportEntry(String description, String result, boolean isVerbose) {
        this.description = description;
        this.result = result;
        this.isVerbose = isVerbose;
    }

    public ReportEntry() {
        description = "";
        result = "";
        isVerbose = false;
    }

    public String getDescription() {
        return description;
    }

    public void setDescription(String description) {
        this.description = description;
    }

    public String getResult() {
        return result;
    }

    public void setResult(String result) {
        this.result = result;
    }

    public boolean isVerbose() {
        return isVerbose;
    }

    public void setVerbose(boolean verbose) {
        isVerbose = verbose;
    }
}
